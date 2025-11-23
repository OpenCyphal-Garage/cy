#!/usr/bin/env python3

"""
Monte‑Carlo simulation for the Optimistic DAD node-ID assignment protocol.
Node-IDs are integers in the range [0, M]. There are N nodes.
Whenever two or more nodes share the same ID, any individual member of that collision group redraws with independent
probability q in (0 < q <= 1).
A redraw means picking a fresh ID uniformly at random from [0, M].

The adjustable parameter q affects the convergence speed of the protocol.
It can be shown that the protocol converges in fewer steps if q is 1 and N<<M;
however, if N is large relative to M, then q=0.5 performs better.
Practical implementations may either choose constant q=0.5 to ensure more consistent performance in both large and small
networks, or to reduce q after every collision or with uptime down to some lower threshold (~0.25)
to let old nodes stick to their IDs while forcing newcomers to redraw.
"""

import random
import argparse
import statistics
from collections import Counter


def simulate_once(
    N: int,
    M: int,
    q: float,
    max_steps: int = 10_000,
    *,
    _rand: random.Random = random,
) -> int:
    """
    Returns the number of rounds until convergence (every participant has a unique identifier).
    Zero means the initial random draw was already collision‑free.
    """
    ids: list[int] = [_rand.randint(0, M) for _ in range(N)]
    for step in range(max_steps + 1):  # step = 0 is the initial state
        if len(set(ids)) == N:
            return step  # convergence achieved
        counts: Counter = Counter(ids)
        for i, ident in enumerate(ids):
            if counts[ident] > 1 and _rand.random() < q:
                ids[i] = _rand.randint(0, M)
    raise RuntimeError("Maximum steps exceeded before convergence")


def run_sim(
    trials: int,
    N: int,
    M: int,
    q: float,
    K: int | None = None,
    *,
    seed: int | None = None,
) -> dict[str, object]:
    """
    Run independent simulations and collect summary statistics.
    If K is provided, also compute the probability that the process terminates within K steps.
    """
    rnd = random.Random(seed) if seed is not None else random
    steps_list: list[int] = [simulate_once(N, M, q, _rand=rnd) for _ in range(trials)]
    mean_steps = statistics.fmean(steps_list)
    prob_within_K = None if K is None else sum(s <= K for s in steps_list) / trials
    return {
        "mean_steps": mean_steps,
        "prob_within_K": prob_within_K,
        "distribution": steps_list
    }


def sweep_q(
    trials: int,
    N: int,
    M: int,
    q_values: list[float],
    K: int | None = None,
    *,
    seed: int | None = None,
) -> list[tuple[float, float, float|None]]:
    """
    Evaluate several q parameters with identical settings.
    Returns a list of (q, mean_steps, prob_within_K) tuples sorted by *q*.
    """
    rows = []
    for q in q_values:
        stats = run_sim(trials, N, M, q, K, seed=seed)
        rows.append((q, stats["mean_steps"], stats["prob_within_K"]))
    return rows


# noinspection PyTypeChecker
def _cli():
    parser = argparse.ArgumentParser(
        description="Monte‑Carlo exploration of Optimistic DAD",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--trials", type=int, default=10_000, help="number of Monte‑Carlo runs")
    parser.add_argument("--N", type=int, required=True, help="number of nodes")
    parser.add_argument("--M", type=int, required=True, help="node-ID range [0,M]")
    parser.add_argument("--q", type=float, default=0.5, help="redraw probability for a colliding node (0<q≤1)")
    parser.add_argument("--K", type=int, default=None, help="report probability that convergence ≤K steps")
    parser.add_argument("--seed", type=int, default=None, help="PRNG seed for reproducibility")
    args = parser.parse_args()

    stats = run_sim(args.trials, args.N, args.M, args.q, args.K, seed=args.seed)

    print("\n===== Monte‑Carlo results =====")
    print(f"trials                     : {args.trials}")
    print(f"participants (N)           : {args.N}")
    print(f"identifier max (M)         : {args.M}")
    print(f"redraw probability (q)     : {args.q}")
    print(f"average steps to converge  : {stats['mean_steps']:.3f}")
    if args.K is not None:
        print(f"P(converge ≤ {args.K} steps) : {stats['prob_within_K']:.4f}")

    # Small histogram up to the 99th percentile for a quick visual check
    from math import ceil
    cutoff = ceil(statistics.quantiles(stats["distribution"], n=100)[98])
    hist = Counter(s for s in stats["distribution"] if s <= cutoff)
    print("\nstep  runs (≤99th percentile)")
    for step in range(max(hist) + 1):
        bar = "*" * (hist[step] * 50 // max(hist.values())) if hist else ""
        print(f"{step:4d}  {hist[step]:6d} {bar}")


if __name__ == "__main__":
    _cli()
