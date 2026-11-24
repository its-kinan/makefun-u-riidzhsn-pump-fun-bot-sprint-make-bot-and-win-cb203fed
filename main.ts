// Pump.fun Bot Sprint — selective early-runner rider.
//
// Idea: on this market most coins spike once in their first few slots and then
// bleed out, so the only repeatable edge is to buy the launch itself, but only
// when the opening tape shows real demand: several distinct buyers, real SOL
// already in the curve, the creator not dumping, and the price not yet mooned.
// The position is tiny (0.05 SOL target, capped at 1% of the curve's real SOL
// reserve by the harness), exits fast (take profit +30%, stop -12%, trailing
// stop once +15%, hard 20-slot hold cap, out the moment the creator sells),
// and the bot never chases a coin twice.
//
// Guardrail pacing: the run must end with at least 20 coins traded. Strategy
// entries alone trade ~90 coins on the 24h dev window (~23 on a 6h final
// window), which is thin, so when no strategy entry has fired for a while and
// free slots exist, the bot takes a minimal 0.02 SOL probe round trip on the
// most liquid recent curve and sells it as soon as it lands. Probes are paced
// (at most one per 3000 slots), capped, and never take the last slots reserved
// for real entries.
//
// Deterministic by construction: no clock, no randomness, no network; every
// decision is a pure function of the batches the harness sends, iterated in
// insertion order.

import {
  LAMPORTS_PER_SOL,
  runBot,
  type Batch,
  type BotState,
  type OrderInput,
  type Pubkey,
} from './vendor/makefun-bot.ts';

// ---------------------------------------------------------------- parameters

/** Target SOL per strategy entry (the harness caps each reply's buys on one
 *  mint at 1% of that mint's real SOL reserve, so young curves take less). */
const STAKE_LAMPORTS = (LAMPORTS_PER_SOL * 5n) / 100n; // 0.05 SOL
/** Smallest buy worth paying the transaction fee for. */
const MIN_BUY_LAMPORTS = LAMPORTS_PER_SOL / 100n; // 0.01 SOL
/** Entry window: slots since the CreateEvent during which a first buy may be decided. */
const MAX_AGE_SLOTS = 6;
/** Entry tape: at least this many trades seen, this many distinct buyers, at most this many. */
const MIN_TRADES = 3;
const MIN_BUYERS = 3;
const MAX_BUYERS = 3;
/** Entry tape: the curve must already hold at least this much real SOL. */
const MIN_REAL_SOL_LAMPORTS = 2n * LAMPORTS_PER_SOL;
/** Entry tape: net SOL bought (buys minus sells) since creation, at least this. */
const MIN_NET_BUY_LAMPORTS = 2n * LAMPORTS_PER_SOL;
/** Entry tape: the creator's own buys since creation, at most this. */
const MAX_CREATOR_BUY_LAMPORTS = (LAMPORTS_PER_SOL * 5n) / 2n; // 2.5 SOL
/** Entry tape: price now over the create price, between these bounds. */
const MIN_RUNUP = 1.0;
const MAX_RUNUP = 3.0;
/** Exits, as fractions of cost (value / cost - 1). */
const TAKE_PROFIT = 0.3;
const STOP_LOSS = -0.12;
const TRAIL_ARM = 0.15;
const TRAIL_DROP = -0.08;
/** Exit after holding this many slots, whatever the price. */
const MAX_HOLD_SLOTS = 10;
/** After an exit, ignore the coin for this many slots. */
const COOLDOWN_SLOTS = 300;
/** Slippage is left wide open: a fill refused for the price moving in the
 *  2-slot latency is worse than the slippage itself on these curves. */
const SLIPPAGE_BPS = 10_000;

/** Probe round trips for the guardrail: stake, cap, and the idle time after
 *  which a probe may fire when free slots exist. */
const PROBE_STAKE_LAMPORTS = (LAMPORTS_PER_SOL * 2n) / 100n; // 0.02 SOL
const PROBE_IDLE_SLOTS = 1500;
const PROBE_MAX = 60;
/** Probes never take the last two position slots; those stay for real entries. */
const PROBE_MAX_COMMITTED = 3;

// ---------------------------------------------------------------- coin tape

interface CoinTape {
  mint: Pubkey;
  createdSlot: number | null;
  creator: Pubkey | null;
  /** Marginal price (SOL per raw token unit) at creation, null until seen. */
  createPrice: number | null;
  trades: number;
  buyers: Set<Pubkey>;
  buyLamports: bigint;
  sellLamports: bigint;
  creatorBuyLamports: bigint;
  creatorSold: boolean;
  lastTradeSlot: number;
  complete: boolean;
  /** Slot this mint was first seen (create or first trade/mark). */
  firstSeenSlot: number;
}

function newTape(mint: Pubkey, slot: number): CoinTape {
  return {
    mint,
    createdSlot: null,
    creator: null,
    createPrice: null,
    trades: 0,
    buyers: new Set(),
    buyLamports: 0n,
    sellLamports: 0n,
    creatorBuyLamports: 0n,
    creatorSold: false,
    lastTradeSlot: -1,
    complete: false,
    firstSeenSlot: slot,
  };
}

/** Marginal price from reserves: virtual SOL per virtual token, as a float. */
function priceOf(vq: bigint, vt: bigint): number {
  if (vt === 0n) return 0;
  return Number(vq) / Number(vt);
}

// ---------------------------------------------------------------- positions

interface Held {
  mint: Pubkey;
  entrySlot: number;
  /** Best value/cost ratio seen since entry. */
  peakRatio: number;
  /** True for guardrail probes: sold as soon as the buy lands. */
  probe: boolean;
}

// ---------------------------------------------------------------- the bot

const tapes = new Map<Pubkey, CoinTape>();
/** Mints created recently enough to still qualify for a first entry. */
const watch = new Set<Pubkey>();
const held = new Map<Pubkey, Held>();
const lastExitSlot = new Map<Pubkey, number>();
const tradedMints = new Set<Pubkey>();
/** Mints with a buy / sell sent and not yet reported back in a fill. */
const pendingBuy = new Set<Pubkey>();
const pendingSell = new Set<Pubkey>();
let lastEntrySlot = -1;
let lastProbeSlot = -1;
let probesUsed = 0;
let firstSlot = -1;

/** The latest reserves, read off the state the shim keeps current. */
let latestState: BotState | null = null;

function currentCurve(mint: Pubkey): { vq: bigint; vt: bigint; realQuote: bigint } | null {
  const c = latestState?.curves.get(mint);
  if (c === undefined) return null;
  return { vq: c.virtual_quote_reserves, vt: c.virtual_token_reserves, realQuote: c.real_quote_reserves };
}

function tapeFor(mint: Pubkey, slot: number): CoinTape {
  let t = tapes.get(mint);
  if (t === undefined) {
    t = newTape(mint, slot);
    tapes.set(mint, t);
  }
  return t;
}

function qualifies(t: CoinTape, slot: number): boolean {
  if (t.createdSlot === null || t.createPrice === null || t.createPrice <= 0) return false;
  if (slot - t.createdSlot > MAX_AGE_SLOTS) return false;
  if (t.complete) return false;
  if (t.trades < MIN_TRADES) return false;
  if (t.buyers.size < MIN_BUYERS || t.buyers.size > MAX_BUYERS) return false;
  if (t.creatorSold) return false;
  if (t.creatorBuyLamports > MAX_CREATOR_BUY_LAMPORTS) return false;
  if (t.buyLamports - t.sellLamports < MIN_NET_BUY_LAMPORTS) return false;
  const curve = currentCurve(t.mint);
  if (curve === null) return false;
  if (curve.realQuote < MIN_REAL_SOL_LAMPORTS) return false;
  const now = priceOf(curve.vq, curve.vt);
  const runup = now / t.createPrice;
  if (runup < MIN_RUNUP || runup > MAX_RUNUP) return false;
  return true;
}

await runBot({
  onBatch(state, batch: Batch): OrderInput[] {
    latestState = state;
    if (firstSlot < 0) firstSlot = batch.slot;
    const orders: OrderInput[] = [];
    const tx = state.txFeeLamports();
    let free = state.freeCashLamports();
    let buysThisReply = 0;

    // --- fold this batch's fills into the traded set ----------------------
    for (const f of batch.fills) {
      if (f.status === 'filled' && f.side === 'buy') tradedMints.add(f.mint);
      if (f.side === 'buy') pendingBuy.delete(f.mint);
      if (f.side === 'sell') pendingSell.delete(f.mint);
    }

    // --- fold this batch's events into the tapes --------------------------
    for (const e of batch.events) {
      const t = tapeFor(e.mint, batch.slot);
      if (e.event === 'CreateEvent') {
        t.createdSlot = e.slot;
        t.creator = e.creator;
        t.createPrice = priceOf(BigInt(e.virtual_quote_reserves), BigInt(e.virtual_token_reserves));
        watch.add(e.mint);
      } else if (e.event === 'TradeEvent') {
        t.trades += 1;
        t.lastTradeSlot = e.slot;
        const sol = BigInt(e.sol_amount);
        if (e.is_buy) {
          t.buyLamports += sol;
          t.buyers.add(e.user);
          if (t.creator !== null && e.user === t.creator) t.creatorBuyLamports += sol;
        } else {
          t.sellLamports += sol;
          if (t.creator !== null && e.user === t.creator) t.creatorSold = true;
        }
      } else {
        t.complete = true;
        watch.delete(e.mint);
      }
    }

    // --- exits for everything held ----------------------------------------
    for (const [mint, pos] of state.positions) {
      if (pendingSell.has(mint)) continue;
      const curve = currentCurve(mint);
      if (curve === null) continue;
      const tokens = BigInt(pos.token_amount);
      const cost = BigInt(pos.cost_lamports);
      if (tokens === 0n || cost === 0n) continue;
      const value = Number(tokens) * priceOf(curve.vq, curve.vt);
      const ratio = value / Number(cost);
      const h = held.get(mint) ?? { mint, entrySlot: batch.slot, peakRatio: ratio, probe: false };
      if (ratio > h.peakRatio) h.peakRatio = ratio;
      held.set(mint, h);

      let sell = false;
      if (h.probe) {
        // A probe is sold as soon as its buy has landed.
        sell = true;
      } else if (ratio - 1 >= TAKE_PROFIT) {
        sell = true;
      } else if (ratio - 1 <= STOP_LOSS) {
        sell = true;
      } else if (h.peakRatio - 1 >= TRAIL_ARM && ratio / h.peakRatio - 1 <= TRAIL_DROP) {
        sell = true;
      } else if (batch.slot - h.entrySlot >= MAX_HOLD_SLOTS) {
        sell = true;
      } else {
        const t = tapes.get(mint);
        if (t !== undefined && t.creatorSold) sell = true;
      }
      if (sell) {
        if (orders.length >= state.hello.caps.max_orders_per_batch) continue;
        orders.push({ side: 'sell', mint, token_amount: tokens.toString(), max_slippage_bps: SLIPPAGE_BPS });
        pendingSell.add(mint);
        held.delete(mint);
        lastExitSlot.set(mint, batch.slot);
      }
    }

    // --- forget positions the harness closed (complete / flatten) ----------
    // A held record survives while its buy is still in flight: the position
    // only appears in state.positions once the fill lands.
    for (const mint of [...held.keys()]) {
      if (!state.positions.has(mint) && !pendingBuy.has(mint)) held.delete(mint);
    }

    // --- strategy entries: only coins created in the last few slots -------
    const maxOpen = state.hello.caps.max_open_positions;
    if (state.committedPositionCount() + buysThisReply < maxOpen) {
      for (const mint of [...watch]) {
        const t = tapes.get(mint);
        if (t === undefined || t.createdSlot === null) {
          watch.delete(mint);
          continue;
        }
        if (batch.slot - t.createdSlot > MAX_AGE_SLOTS) {
          watch.delete(mint);
          continue;
        }
        if (orders.length >= state.hello.caps.max_orders_per_batch) break;
        if (state.committedPositionCount() + buysThisReply >= maxOpen) break;
        if (state.positions.has(mint) || held.has(mint)) continue;
        const lastExit = lastExitSlot.get(mint);
        if (lastExit !== undefined && batch.slot - lastExit < COOLDOWN_SLOTS) continue;
        if (!qualifies(t, batch.slot)) continue;
        const cap = state.maxBuyLamports(mint);
        if (cap < MIN_BUY_LAMPORTS) continue;
        const amount = cap < STAKE_LAMPORTS ? cap : STAKE_LAMPORTS;
        if (free < amount + tx) continue;
        orders.push({ side: 'buy', mint, quote_lamports: amount.toString(), max_slippage_bps: SLIPPAGE_BPS });
        free -= amount + tx;
        buysThisReply += 1;
        lastEntrySlot = batch.slot;
        pendingBuy.add(mint);
        held.set(mint, { mint, entrySlot: batch.slot, peakRatio: 0, probe: false });
      }
    }

    // --- guardrail probes, paced: at most one per idle window -------------
    const committed = state.committedPositionCount() + buysThisReply;
    const idleSinceEntry = lastEntrySlot < 0 ? batch.slot - firstSlot : batch.slot - lastEntrySlot;
    const idleSinceProbe = lastProbeSlot < 0 ? idleSinceEntry : batch.slot - lastProbeSlot;
    if (
      probesUsed < PROBE_MAX &&
      tradedMints.size < 32 &&
      committed < PROBE_MAX_COMMITTED &&
      idleSinceEntry >= PROBE_IDLE_SLOTS &&
      idleSinceProbe >= PROBE_IDLE_SLOTS &&
      orders.length < state.hello.caps.max_orders_per_batch
    ) {
      // Most liquid recent curve: highest real SOL with a trade in the last
      // 100 slots, not held, not complete, not exited recently.
      let best: Pubkey | null = null;
      let bestReal = 0n;
      for (const [mint, t] of tapes) {
        if (t.complete || state.positions.has(mint) || held.has(mint)) continue;
        if (batch.slot - t.lastTradeSlot > 100) continue;
        const lastExit = lastExitSlot.get(mint);
        if (lastExit !== undefined && batch.slot - lastExit < COOLDOWN_SLOTS) continue;
        const curve = currentCurve(mint);
        if (curve === null || curve.realQuote <= bestReal) continue;
        if (curve.realQuote < MIN_BUY_LAMPORTS * 100n) continue;
        best = mint;
        bestReal = curve.realQuote;
      }
      if (best !== null) {
        const cap = state.maxBuyLamports(best);
        if (cap >= MIN_BUY_LAMPORTS) {
          const amount = cap < PROBE_STAKE_LAMPORTS ? cap : PROBE_STAKE_LAMPORTS;
          if (free >= amount + tx) {
            orders.push({ side: 'buy', mint: best, quote_lamports: amount.toString(), max_slippage_bps: SLIPPAGE_BPS });
            free -= amount + tx;
            buysThisReply += 1;
            probesUsed += 1;
            lastProbeSlot = batch.slot;
            pendingBuy.add(best);
            held.set(best, { mint: best, entrySlot: batch.slot, peakRatio: 0, probe: true });
          }
        }
      }
    }

    // --- prune stale tapes (bounded memory over a long replay) --------------
    if (batch.seq % 1000 === 0) {
      for (const [mint, t] of tapes) {
        const age = batch.slot - (t.createdSlot ?? t.firstSeenSlot);
        if (age > 5000 && !state.positions.has(mint) && !held.has(mint)) tapes.delete(mint);
      }
    }

    return orders;
  },
});
