# Convergence proof for topic allocation CRDT

The model applies to:
- the formal operators in `Core.tla` (`AllocateTopic`, `AcceptGossip`, `Converged`);
- the implementation in `cy/cy.c` (`topic_allocate`, `on_gossip_known_topic`, `on_gossip_unknown_topic`),
  under the assumptions listed below.

## Model

Let:

- $H$ be the finite set of active topic hashes, $|H| = N$.
- $U$ be the finite set of auto-assigned subject-IDs, $|U| = M$.
- $S: H \times \mathbb{N} \to U$ be the deterministic subject-ID mapping function.
- A topic record be $(h, e, a)$ where $h \in H$, $e \in \mathbb{N}$ (evictions), $a \in \mathbb{N}$ (age).
- $\ell(a) = \lfloor \log_2(a) \rfloor$ with $\ell(0) = -1$.

Definitions:

- Collision: two records with different hashes mapped to the same subject-ID.
- Divergence: two records with the same hash but different evictions.
- Converged state: no collisions and no divergences.

The following assumptions apply; some are not runtime-enforced and are therefore required as deployment constraints.

### A1. Common deterministic mapping

All nodes use the same deterministic $S(h,e)$ and the same mapping parameters (e.g., modulus).

### A2. Hash identity

Active topic names are hash-unique (or equivalently: equal hash means same logical topic).
Hash collision probability is negligible.

### A3. Bounded escape property

There exists $K \in \mathbb{N}_{>0}$ such that:

$$
\forall h \in H,\ \forall x \in \mathbb{N},\ \forall B \subseteq U,\ |B| < K,\
\exists d \in \{0,\dots,K-1\}: S(h, x+d) \notin B.
$$

I.e., from any current eviction value, a topic can escape any blocked subject-ID set smaller than $K$ within at most $K$ increments.

### A4. Capacity bound

$$
N \le K.
$$

### A5. Gossip fairness

Every live allocation entry is eventually received and processed by every relevant node infinitely often.

### A6. Progress fairness

Each node keeps executing the protocol loop (no permanent local halt while the node is considered active).

### A7. Resource sufficiency

Memory/stack/scheduler resources are sufficient for processing and for completing each local allocation cascade.

### A8. Eviction counter safety

Eviction counters do not overflow in reachable executions.

### A9. Stability window (timescale separation)

There exists a repair bound $T_{\mathrm{repair}}$ and time windows of length $> T_{\mathrm{repair}}$ where:

- active topic set $H$ is unchanged;
- mapping function parameters are unchanged;
- pairwise arbitration outcomes do not flip (priority order is effectively stable over the window).

I.e., arbitration priority flips due to $\lfloor{}\log(a)\rfloor{}$ increments are much less frequent than gossip+repair dynamics.

## Theorem 1: Convergence in one stability window

Under stated assumptions, any execution restricted to one stability window converges in finite time to a collision-free, non-divergent state.

### Lemma 1: local allocation termination under bounded escape

Fix a node and a moving topic hash $h$ with current eviction $x$.
Let $B$ be the set of currently occupied subject-IDs by other local topics.
If $|B| < K$, then by A3 there exists $d < K$ such that $S(h, x+d) \notin B$.

`AllocateTopic`/`topic_allocate` increments the moving topic eviction by one exactly when it loses arbitration on its current candidate subject.
Therefore within at most $d$ losses it reaches a candidate not in $B$, and insertion terminates.

So local allocation terminates whenever $|B| < K$. By A4, $|B| \le N-1 < K$.

### Lemma 2: divergence repair converges for each hash

For fixed hash $h$, `AcceptGossip` on the known-hash path compares local and remote replicas using divergence arbitration and either:

- keeps local evictions (plus age merge), or
- adopts remote evictions and re-allocates.

Under A5 and a stable window (A9), each node repeatedly observes the same finite set of contenders for $h$
and eventually agrees on the same winning replica for $h$ (same eviction value and consistent merged age level).
Hence divergences for $h$ disappear in finite time.

Applying this independently to each $h \in H$, all divergences disappear in finite time.

### Lemma 3: collision repair converges under stable priorities

In a stability window (A9), collision arbitration induces a fixed strict total order on active hashes:

$$
h_1 \succ h_2 \succ \dots \succ h_N.
$$

When $h_i$ collides with any $h_j$ where $j < i$, $h_i$ loses and is evicted; $h_j$ is unchanged.
So higher-priority topics are never displaced by lower-priority topics.

Induction on priority rank:

- Base $i=1$: $h_1$ cannot be displaced by anyone, so once allocated it remains fixed.
- Step: assume $h_1,\dots,h_{i-1}$ fixed at subject set $B_i$ ($|B_i|=i-1<K$ by A4).
  By A3, from current eviction $x_i$ topic $h_i$ has some $d_i < K$ with
  $S(h_i, x_i+d_i) \notin B_i$.
  Each loss against $B_i$ increments eviction by one, so after finitely many losses ($\le d_i$) $h_i$ reaches a
  subject outside $B_i$ and then cannot be displaced by lower-priority topics.

Thus every $h_i$ stabilizes in finite time, and all collisions disappear.

### Conclusion

By Lemma 2, divergences vanish in finite time.
By Lemma 3, collisions vanish in finite time.
Therefore the state becomes converged (no collisions, no divergences) in finite time.

## Theorem 2: Convergence with occasional priority flips

Assume A1-A8 and that executions consist of stability windows as in A9, each longer than $T_{\mathrm{repair}}$.
Then the network converges within each window;
non-converged periods are transient and confined to window transitions (including in-flight stale gossip effects).

### Proof sketch

Apply Theorem 1 independently to each stability window.
Window transitions may re-introduce temporary conflicts,
but the next stable window repairs them before the next flip by construction ($\text{window length} > T_{\mathrm{repair}}$).

## Instantiating A3/A4 for common probing laws

Linear probing ($S(h,e) = h+e \pmod M$): A3 holds with $K=M$. Used in the TLA+ model for legibility.

Quadratic probing (current implementation):
the protocol relies on the deployment bound that active non-pinned topics do not exceed the collision-free probing capacity;
practically this is the half-ring bound discussed in the design docs,
i.e. approximately $K \approx \lfloor M/2 \rfloor + 1$ and thus $N \le \lfloor M/2 \rfloor$.
