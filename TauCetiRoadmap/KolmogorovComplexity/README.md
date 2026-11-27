# Roadmap: plain and prefix-free Kolmogorov complexity

**Summary.** The Kolmogorov complexity of a finite binary string is the length of its shortest
description, where descriptions are decoded by a fixed partial computable map from strings to
strings. This roadmap defines the complexity relative to any such description map, with the value
infinity for a string that has no description, and develops the classical theory of plain
complexity and of prefix-free complexity, following Shen, Uspensky and Vereshchagin.

The headline theorems are these.

- *Invariance.* Some partial computable description map is optimal: its complexities exceed
  those of any other partial computable description map by at most a constant.
  For an optimal map, the complexity of a string is at most its length plus a constant, and
  applying a partial computable map to a string raises its complexity by at most a constant.
- *Counting.* For every description map and every `k`, fewer than `2^k` strings have complexity
  below `k`. So at every length `n` some string has complexity at least `n`, and for `c ≤ n`
  fewer than a fraction `2^(−c)` of the strings of length `n` have complexity below `n − c`.
- *Berry's paradox.* For an optimal map, every partial computable function that is a lower
  bound of the complexity on its domain is bounded, the complexity is not computable, and the
  strings whose complexity is less than half their length form a simple set in Post's sense.
- *Prefix-free complexity.* Among the partial computable maps with prefix-free domain there is
  an optimal one. For every map with prefix-free domain the sum of `2^(−K(x))` over the
  describable strings is at most `1`, so `K(x) ≤ |x| + c` fails for every constant `c`; and
  `C(x) ≤ K(x) + c` and `K(x) ≤ C(x) + 2 log₂ C(x) + c` for optimal maps.

The roadmap builds on Mathlib's partial recursive functions and their universal evaluation of
codes, on Mathlib's prefix-free sets of words with Kraft's inequality, and on the simple sets of
Tau Ceti's computability library, which realise the immune and simple sets of the roadmap
ComputabilityTheory. Algorithmic randomness of infinite sequences, conditional complexity and the
coding theorem are not treated.

Layer 1 defines complexity and optimality and proves the invariance theorem with the basic upper
bounds. Layer 2 counts strings of small complexity and proves the converse for enumerable
families. Layer 3 proves upper semicomputability, Berry's paradox and the simplicity of the set of
compressible strings. Layer 4 treats prefix-free description maps.

## Conventions

1. **Strings.** A string is `List Bool`; `|x|` is `x.length`; `[]` is the empty string. A
   *description map* is a partial function `D : List Bool →. List Bool`, and `p` is a
   description of `x` when `x ∈ D p`. Computability is Mathlib's: `Partrec`, `Computable` and
   `REPred` for the `Primcodable` instances of `List Bool`, `ℕ` and their products.
2. **Complexity.** `descComplexity D x : ℕ∞` is the infimum of `|p|` over the descriptions `p`
   of `x`; it is `⊤` when `x` has no description. No statement uses a junk value: where a
   complexity is compared with a natural number, the comparison is in `ℕ∞`, and the only
   `ENat.toNat` (4.2) is taken on strings of finite complexity. Plain complexity `C` is
   `descComplexity U` for an optimal description map `U`; prefix-free complexity `K` is
   `descComplexity D` for an optimal prefix-free map `D`. Two optimal maps give complexities that
   differ by a bounded amount, so every theorem is stated for an arbitrary optimal map.
3. **Constants.** Constants `c` are natural numbers and depend on the maps, never on strings.
   Logarithms are `Nat.log 2`, with `Nat.log 2 0 = 0`.
4. **Prefix-free.** A set of strings is prefix-free in Mathlib's sense
   `InformationTheory.IsPrefixFree`: no element is a prefix of a different element. The empty
   set is prefix-free, and so is `{[]}`.

## Layer 1: complexity, optimality and invariance

### 1.1 Complexity relative to a description map

Define `descComplexity D x = ⨅ (p) (_ : x ∈ D p), (|p| : ℕ∞)`, and the structure
`IsOptimalDescriptionMap D`: `D` is partial computable, and for every partial computable `D'`
there is `c : ℕ` with `descComplexity D x ≤ descComplexity D' x + c` for all `x`.

**Checks.**
- The identity map has `descComplexity id x = |x|`; the constant map with value `[true, false]`
  gives `[true, false]` complexity `0` and every other string complexity `⊤`; the nowhere-defined
  map gives every string complexity `⊤`.
- A variant valued in `ℕ` through `sInf` (with `sInf ∅ = 0`) would give every string complexity
  `0` for the nowhere-defined map, and the counting bound 2.1 would fail at `k = 1`.
- In the infimum, a description of minimal length exists whenever the value is finite, since
  `ℕ∞` is well-ordered; for a partial computable map the minimum is not computable in general
  (3.2).

*Needs:* Mathlib `Partrec`, `Part`.

### 1.2 The invariance theorem

`exists_isOptimalDescriptionMap`: there is an optimal description map [SUV, Thm. 1 (Solomonoff–
Kolmogorov), p. 13].

(Proved here, by the construction of the cited proof with a unary header.) Every string with a
`false` entry is uniquely `1^e 0 q`: `e` entries `true`, then `false`, then `q`. Put
`U(1^e 0 q) = (eval (ofNat Code e) (encode q)).bind (decode as a string)` and leave `U`
undefined on the strings `1^e`. The header is read by a primitive recursive split, `ofNat Code`
and `decode` are primitive recursive, and `Nat.Partrec.Code.eval` is partial computable in both
arguments, so `U` is partial computable. Given a partial computable `D'`, the function
`n ↦ (decode n).bind (fun a ↦ (D' a).map encode)` is partial recursive by the definition of
`Partrec`, so it is `eval c` for a code `c` (`Nat.Partrec.Code.exists_code`). With
`e = encode c`, `Encodable.encodek` gives `U(1^e 0 q) = D' q` for every `q`. A description `q` of
`x` for `D'` thus yields the description `1^e 0 q` for `U` of length `|q| + e + 1`, so
`descComplexity U x ≤ descComplexity D' x + (e + 1)`; this is trivial when the right side is `⊤`.

**Checks.**
- The header must add a constant to the length. Prefixing the code number through `Nat.pair`
  does not: `Nat.pair e n = n² + e` for `e < n`, and for `e = 5` and `n = 2^j` the bit length of
  `Nat.pair 5 n` exceeds that of `n` by `4, 9, 14, …, 39` for `j = 4, 9, 14, …, 39`.
- The unary headers `1^e 0` form a prefix-free set, so `1^e 0 q = 1^f 0 r` forces `e = f` and
  `q = r`; the split recovers `(e, q)` on all strings of length at most `12`.

*Needs:* Mathlib `Nat.Partrec.Code.eval`, `Nat.Partrec.Code.eval_part`,
`Nat.Partrec.Code.exists_code`, `Primrec.ofNat`, `Primrec.decode`, `Encodable.encodek`,
`Partrec.bind`, `Partrec.comp`.

### 1.3 Length bound and algorithmic transformations

`IsOptimalDescriptionMap.upper_bounds`: let `D` be optimal. Then (a) there is `c` with
`descComplexity D x ≤ |x| + c` for all `x` [SUV, Thm. 2, p. 15]; in particular every string has
finite complexity. (b) For every partial computable `A : List Bool →. List Bool` there is `c`
with `descComplexity D y ≤ descComplexity D x + c` whenever `y ∈ A x` [SUV, Thm. 3, p. 15].

(Proved here, as in the cited proofs.) (a) The identity is computable, hence partial computable
(`Computable.partrec`), and `x` describes itself, so its complexity for the identity is at most
`|x|`; apply optimality. (b) The map `p ↦ (D p).bind A` is partial computable (`Partrec.bind`);
if `x ∈ D p` and `y ∈ A x` then `y ∈ (D p).bind A`, so the complexity of `y` for this map is at
most `descComplexity D x`; apply optimality.

*Needs:* 1.1; Mathlib `Computable.partrec`, `Partrec.bind`.

### Examples

- Reversing a string, or doubling each of its bits, changes the complexity by at most a constant,
  by 1.3(b) applied to the map and to its partial computable inverse.

### Dependencies

1.2 and 1.3 use 1.1 and Mathlib.

## Layer 2: counting

### 2.1 Few strings have small complexity

`descComplexity_counting`: for every description map `D`, computable or not,
(a) for every `k` the set `{x | descComplexity D x < k}` has `encard < 2^k`;
(b) for every finite set `A` and every `k`,
`#A + 1 ≤ #{x ∈ A | k ≤ descComplexity D x} + 2^k`;
(c) for every `n` some `x` with `|x| = n` has `n ≤ descComplexity D x`.
Statement (a) is [SUV, Thm. 5, p. 18] for optimal maps; its proof uses nothing about `D`.

(Proved here.) If `descComplexity D x < k`, the infimum is below `k`, so (`iInf_lt_iff`) some
description `p_x` of `x` has `|p_x| < k`. A description describes one string at most
(`Part.mem_unique`), so `x ↦ p_x` is injective into the strings of length less than `k`, of which
there are `1 + 2 + ⋯ + 2^(k−1) = 2^k − 1`. This gives (a). For (b), split `A` into the elements
of complexity below `k`, at most `2^k − 1` of them by (a), and the rest. For (c), take for `A`
the `2^n` strings of length `n` and `k = n` in (b): at least one element has complexity at least
`n`.

**Checks.**
- For the identity map, exactly `2^k − 1` strings have complexity below `k`, so (a) is sharp.
- On all strings of length at most `10`, for the identity, the constant map of 1.1 and the map
  `p ↦ (first ⌊(2|p| + 1)/3⌋ entries of reverse p ++ p)`, undefined when `|p| ≡ 2 (mod 3)`: the
  bound of (a) holds for `k ≤ 10`, (b) holds for the sets of strings of each length `n ≤ 6`, and
  (c) holds for `n ≤ 10`.

*Needs:* 1.1; Mathlib `iInf_lt_iff`, `Part.mem_unique`, `Set.encard`.

### 2.2 Enumerable families of small sets

`IsOptimalDescriptionMap.exists_lt_add_of_rePred`: let `D` be optimal and `V ⊆ ℕ × List Bool` c.e.,
with `{x | (n, x) ∈ V}.encard < 2^n` for every `n`. Then there is `c` with
`descComplexity D x < n + c` whenever `(n, x) ∈ V` [SUV, Thm. 7(b), p. 31].

(Proved here, following the cited proof.) Since `V` is c.e., the function on pairs that is
defined exactly on `V` is `eval e` composed with `encode` for a code `e`. Let `G_s` be the set of
pairs `v` with `evaln s e (encode v)` defined; `G_s` is finite (`Nat.Partrec.Code.evaln_bound`),
increasing in `s` (`Nat.Partrec.Code.evaln_mono`), decidable uniformly in `s`
(`Nat.Partrec.Code.primrec_evaln`), and its union is `V` (`Nat.Partrec.Code.evaln_complete`).
Order `V` by the first stage at which a pair enters, and within a stage by `encode`. For each
`n`, list the strings `x` with `(n, x) ∈ V` in this order as `x_0, x_1, …`, fewer than `2^n` of
them. For a string `y`, let `r(y) = Σ_i [y_i] 2^i < 2^|y|`; on strings of length `n` this is a
bijection onto `{0, …, 2^n − 1}`. Define `D_V(y) = x_{r(y)}` for `n = |y|`, undefined when that
term does not exist. To compute it, search for the least `s` such that `G_s` contains more than
`r(y)` pairs with first component `|y|`, and output the `r(y)`-th of them in the order; pairs
entering after stage `s` come later in the order, so this is `x_{r(y)}`. So `D_V` is partial
computable. Every `x` with `(n, x) ∈ V` is `x_j` for some `j < 2^n`, hence `D_V(y) = x` for the
`y` of length `n` with `r(y) = j`, and `descComplexity D_V x ≤ n`. Optimality gives `c'` with
`descComplexity D x ≤ n + c' < n + (c' + 1)`.

**Checks.**
- Enumerability cannot be dropped: by 2.1(c) choose for each `n ≥ 1` a string `x_n` of length
  `2n` with `2n ≤ C(x_n)`; the family with empty `0`-th set and `n`-th set `{x_n}` satisfies the
  cardinality bound, and `C(x_n) < n + c` fails for `n ≥ max(c, 1)`.
- The cardinality bound cannot be dropped: the family whose `n`-th set is all strings of length
  `2n` is decidable and contains the same `x_n`.

*Needs:* 1.1; Mathlib `REPred`, `Nat.Partrec.Code.evaln`, `Nat.Partrec.Code.evaln_bound`,
`Nat.Partrec.Code.evaln_mono`, `Nat.Partrec.Code.evaln_complete`,
`Nat.Partrec.Code.primrec_evaln`, `Nat.Partrec.Code.exists_code`, `Partrec.rfind`.

### Examples

- Fewer than `2^90` strings of length `100` have complexity below `90`, a fraction below
  `2^(−10)` (2.1(a)).
- For every description map and `c ≤ n`, at least `2^n − 2^(n−c) + 1` strings of length `n` have
  complexity at least `n − c` (2.1(b) with `k = n − c`).

### Dependencies

2.1 uses 1.1; 2.2 uses 1.1 and Mathlib's bounded evaluation of codes.

## Layer 3: algorithmic properties

### 3.1 Upper semicomputability

`rePred_descComplexity_lt`: for a partial computable `D`, the family of sets
`{x | descComplexity D x < n}` is c.e., that is, the set of pairs `(n, x)` with
`descComplexity D x < n` is c.e. [SUV, Thm. 7(a) and Thm. 8(a), pp. 31–33].

(Proved here.) As in 2.1, `descComplexity D x < n` holds exactly when some `p` with `|p| < n`
has `x ∈ D p`. With a code `c` for the partial recursive function underlying `D` as in 1.2, this
holds exactly when there are `s` and `p` with `|p| < n` and
`evaln s c (encode p) = some (encode x)` (`Nat.Partrec.Code.evaln_complete`,
`Nat.Partrec.Code.evaln_sound`). The search over pairs `(s, p)` by `Partrec.rfind` with this
primitive recursive test (`Nat.Partrec.Code.primrec_evaln`) is a partial computable function of
`(n, x)` whose domain is the relation, which is therefore c.e. (`Partrec.dom_re`).

**Checks.**
- Partial computability of `D` cannot be dropped. Let `D` send the string `1^m` to itself when
  `m = encode c` for a code `c` with `eval c 0` undefined, and be undefined elsewhere. Then
  `descComplexity D 1^m < m + 1` holds exactly for those `m`, and composing with the computable
  `c ↦ (encode c + 1, 1^(encode c))` would make `{c | eval c 0 undefined}` c.e., which
  `ComputablePred.halting_problem_not_re` excludes.

*Needs:* 1.1, 2.1 (the attainment step); Mathlib `Nat.Partrec.Code.evaln_complete`,
`Nat.Partrec.Code.evaln_sound`, `Nat.Partrec.Code.primrec_evaln`, `Partrec.rfind`,
`Partrec.dom_re`.

### 3.2 Berry's paradox

`IsOptimalDescriptionMap.lowerBound_bounded`: let `D` be optimal. (a) If `k : List Bool →. ℕ` is
partial computable and `n ≤ descComplexity D x` whenever `n ∈ k x`, then the values of `k` are
bounded [SUV, Thm. 6, p. 19]. (b) There is no computable `f : List Bool → ℕ` with
`f x = descComplexity D x` for all `x` [SUV, p. 19 and §1.2, p. 35].

(Proved here, following the cited proof with a different description of the large number.)
(a) Suppose the values of `k` are unbounded. Searching over pairs `(s, x)` for one with
`evaln s` of a code of `k` at `encode x` defined with value greater than `N` defines a partial
computable `B : ℕ →. List Bool`, total because `k` is unbounded, with `k(B N) > N`, hence
`N < descComplexity D (B N)`. The map `A(q) = B(2^|q|)` is a partial computable description map,
and every string of length `j` describes `B(2^j)` for `A`, so the complexity of `B(2^j)` for `A`
is at most `j`; optimality gives `c` with `2^j < descComplexity D (B 2^j) ≤ j + c` for all `j`.
At `j = c` this says `2^c < 2c`, which is false for every `c`.
(b) A computable `f` equal to the complexity would be a partial computable lower bound, bounded
by (a), while 2.1(c) gives strings of every complexity at least `n`.

**Checks.**
- Optimality cannot be dropped: for the identity map the complexity is `|x|`, which is
  computable and an unbounded lower bound of itself.
- The search in (a) needs only that `k` is unbounded on its domain; a nowhere-defined `k` is
  bounded by `0`.

*Needs:* 1.1, 2.1; Mathlib `Nat.Partrec.Code.exists_code`, `Nat.Partrec.Code.evaln_complete`,
`Nat.Partrec.Code.primrec_evaln`, `Partrec.rfind`, `Computable.partrec`.

### 3.3 The compressible strings form a simple set

`IsOptimalDescriptionMap.simple_compressible`: let `D` be optimal. The set
`S = {x | 2 · descComplexity D x < |x|}` is simple: c.e., with an infinite complement that has no
infinite c.e. subset (Tau Ceti's `Set.Simple`) [SUV, Thm. 10, p. 36].

(Proved here, following the cited proof.) For a natural number `c` and every `L`,
`2c < L` holds exactly when `c < ⌊(L + 1)/2⌋`, and both fail for `c = ⊤`; so `S` is the preimage
of the relation of 3.1 under the computable map `x ↦ (⌊(|x| + 1)/2⌋, x)`, and is c.e. By 2.1(c)
each length `n` carries a string with `n ≤ descComplexity D x`, hence `2 · descComplexity D x ≥
n`, outside `S`; so the complement is infinite. Let `W` be an infinite c.e. set disjoint from `S`.
The function `k(x) = ⌊|x|/2⌋`, defined exactly on `W`, is partial computable (`W` is the domain
of a partial computable function, by the definition of `REPred`), and on `W` we have
`2 · descComplexity D x ≥ |x|`, hence `k(x) ≤ descComplexity D x`. Only finitely many strings have
bounded length, so `k` is unbounded on the infinite `W`, contradicting 3.2(a).

**Checks.**
- For natural `c, L < 300`, `2c < L` exactly when `c < ⌊(L + 1)/2⌋`, and `2c ≥ L` implies
  `⌊L/2⌋ ≤ c`.
- Optimality cannot be dropped: for the identity map `S` is empty, whose complement, the set of
  all strings, is an infinite c.e. set.

*Needs:* 2.1, 3.1, 3.2; Tau Ceti `Set.Simple`, `Set.Immune`; Mathlib `REPred`.

### Examples

- No partial computable function lists infinitely many strings `x` together with certified lower
  bounds of their complexity tending to infinity: such a list would give an unbounded partial
  computable lower bound, excluded by 3.2(a).

### Dependencies

3.1 uses 1.1 and the attainment step of 2.1; 3.2 uses 1.1 and 2.1; 3.3 uses 2.1, 3.1 and 3.2.

## Layer 4: prefix-free complexity

### 4.1 Prefix-free description maps

Define the structure `IsPrefixFreeDescriptionMap D`: `D` is partial computable and its domain
`{p | (D p).Dom}` is prefix-free; and `IsOptimalPrefixFreeDescriptionMap D`, which extends it: `D` is
prefix-free and for every prefix-free `D'` there is `c` with `descComplexity D x ≤ descComplexity D' x + c`.
`exists_isOptimalPrefixFreeDescriptionMap`: an optimal prefix-free description map exists
[SUV, Thm. 49, p. 97].

(Proved here, following the cited proof, with the unary header of 1.2.) For a code `c`, let the
pairs `(y, z)` with `evaln s c (encode y) = some (encode z)` enter at stage `s`, and order them by
first stage and then by `encode y`; each `y` enters at most once. Keep a pair when `y` is
incomparable (neither is a prefix of the other) with the first component of every pair that comes
before it, and let `{c}(y) = z` for each kept pair `(y, z)`. Then `{c}` is partial computable: to
evaluate it at `y`, search for the stage at which a pair `(y, z)` enters, and compare `y` with the
finitely many first components that entered by that stage. Its domain is prefix-free: of two
kept pairs with comparable first components the later would have been deleted. If the domain of
`eval c` (on encodings of strings) is prefix-free, nothing is deleted and `{c}(y) = D'(y)`, where
`c` codes `D'` as in 1.2. Put `D(1^e 0 y) = {ofNat Code e}(y)`. If `1^e 0 y` is a prefix of
`1^f 0 y'`, then `e = f` (1.2, Checks) and `y` is a prefix of `y'`; both lie in the prefix-free
domain of `{ofNat Code e}`, so they are equal. Optimality: for a prefix-free `D'` with code `c`
and `e = encode c`, `D(1^e 0 y) = D'(y)`, and descriptions grow by `e + 1`.

**Checks.**
- On the enumeration `0 ↦ a`, `01 ↦ b`, `1 ↦ c`, `[] ↦ d`, `110 ↦ e`, `10 ↦ f`, the kept pairs
  are `0 ↦ a` and `1 ↦ c`; on the prefix-free enumeration `0`, `10`, `110`, `111` nothing is
  deleted.
- The identity map is not prefix-free: `[]` is a prefix of every string.

*Needs:* 1.1, 1.2; Mathlib `InformationTheory.IsPrefixFree`, `List.IsPrefix`,
`Nat.Partrec.Code.evaln`, `Nat.Partrec.Code.evaln_complete`, `Nat.Partrec.Code.evaln_bound`,
`Nat.Partrec.Code.primrec_evaln`, `Nat.Partrec.Code.exists_code`.

### 4.2 Kraft's inequality for complexity

`tsum_two_inv_pow_descComplexity_le_one`: if the domain of `D` is prefix-free, then
`∑' x : {x // descComplexity D x ≠ ⊤}, 2⁻¹ ^ (descComplexity D x).toNat ≤ 1` in `ℝ≥0∞`
[SUV, Thm. 57 and its Lemma, p. 106, for optimal prefix-stable maps; the same lemma gives it here].
No computability of `D` is assumed.

(Proved here.) For each `x` of finite complexity choose a description `p_x` of minimal length
(1.1, Checks). The map `x ↦ p_x` is injective (`Part.mem_unique`), and its image `T` lies in the
domain of `D`, so `T` is prefix-free (`InformationTheory.IsPrefixFree.anti`). Reindex the sum
along the bijection onto `T` (`Equiv.tsum_eq`). Mathlib's Kraft inequality over the alphabet
`Bool` (`Fintype.card_bool`) gives a summable real family `(1/2)^|w|` on `T` with sum at most
`1`, and `ENNReal.ofReal_tsum_of_nonneg` carries it to `ℝ≥0∞`.

**Checks.**
- The bound is attained: a map defined only at `[]` has sum `1`.
- Prefix-freeness cannot be dropped: for the identity map the strings of length at most `N`
  contribute exactly `N + 1`.
- For the map that decodes `h(k) ++ p` to `p` for `|p| = k` (header `h` of 4.4), the strings
  described by codes of length at most `13` contribute exactly `45/128`.

*Needs:* 1.1; Mathlib `InformationTheory.IsPrefixFree.anti`,
`InformationTheory.IsPrefixFree.tsum_one_div_card_pow_length_le_one`,
`InformationTheory.IsPrefixFree.summable_one_div_card_pow_length`, `Equiv.tsum_eq`,
`ENNReal.ofReal_tsum_of_nonneg`, `ENNReal.ofReal_pow`, `Fintype.card_bool`, `Part.mem_unique`.

### 4.3 No length bound for prefix-free complexity

`not_exists_descComplexity_le_length_add`: if the domain of `D` is prefix-free, there is no `c`
with `descComplexity D x ≤ |x| + c` for all `x` [SUV, pp. 106–107, after Thm. 57].

(Proved here, as in the cited remark.) Under such a bound every complexity is finite, and the
`2^j` strings of length `j` contribute at least `2^j · 2^(−j−c) = 2^(−c)` to the sum of 4.2. The
strings of length at most `N = 2^c` thus contribute at least `(2^c + 1) · 2^(−c) > 1`, and a finite
partial sum is at most the sum (`sum_le_tsum`), contradicting 4.2.

**Checks.**
- Prefix-freeness cannot be dropped: the identity map has `descComplexity id x = |x|`.
- The nowhere-defined map, whose domain is prefix-free, satisfies the conclusion, since its
  complexities are `⊤`.

*Needs:* 4.2; Mathlib `sum_le_tsum`.

### 4.4 Plain and prefix-free complexity

`IsOptimalPrefixFreeDescriptionMap.compare_plain`: let `U` be optimal and `D` optimal prefix-free.
(a) There is `c` with `descComplexity U x ≤ descComplexity D x + c` for all `x`. (b) There is `c`
with `descComplexity D x ≤ m + 2 · Nat.log 2 m + c` whenever `descComplexity U x ≤ m`; that is,
`K(x) ≤ C(x) + 2 log₂ C(x) + c` [SUV, §4.3, pp. 98–99].

(Proved here, as in the cited remarks, with an explicit header.) (a) `D` is partial computable;
apply the optimality of `U`. (b) For a natural number `k` let `h(k)` be `Nat.bits k` with every
entry doubled, followed by `false, true`; its length is `2 · Nat.size k + 2`
(`Nat.size_eq_bits_len`), and `Nat.size k ≤ Nat.log 2 k + 1` (`Nat.size_le` with
`Nat.lt_pow_succ_log_self`; for `k = 0` both sides are at most `1`). Let `E(s) = U(p)` when
`s = b' ++ [false, true] ++ p`, where `b'` is a list `b` with every entry doubled and
`|p| = Σ_i [b_i] 2^i`, and let `E` be undefined elsewhere. Reading pairs of equal entries until
the first pair `false, true` recovers `b` and then `p`, so `E` is partial computable; and two
strings of this form, one a prefix of the other, share that first pair, hence `b` and `|p|`, and
are equal, so the domain of `E` is prefix-free. Since `Σ_i [b_i] 2^i = k` for `b = Nat.bits k`
(induction with `Nat.bits_append_bit`), a shortest `U`-description `p` of `x`, of length
`k = descComplexity U x ≤ m`, gives the `E`-description `h(k) ++ p` of length
`k + 2 · Nat.size k + 2 ≤ k + 2 · Nat.log 2 k + 4 ≤ m + 2 · Nat.log 2 m + 4`
(`Nat.log_mono_right`). Optimality of `D` gives `c'`, and `c = c' + 4`.

**Checks.**
- For `k ≤ 5000`, `|h(k)| = 2 · Nat.size k + 2` and `k + |h(k)| ≤ k + 2 · Nat.log 2 k + 4`, with
  `Nat.size k = Nat.log 2 k + 1` for `k ≥ 1`; and for `k ≤ m < 400`,
  `k + 2 · Nat.log 2 k ≤ m + 2 · Nat.log 2 m`.
- The codes `h(|p|) ++ p` for the strings `p` of length at most `7` form a prefix-free set and
  decode to `(|p|, p)`.
- Optimality cannot be dropped: the nowhere-defined map is prefix-free and gives `⊤` everywhere,
  so (b) fails for it in place of `D`. Every string has finite prefix-free complexity, through
  the prefix-free map that decodes `x` with every entry doubled, followed by `false, true`, to
  `x`; so (a) fails for the nowhere-defined map, which is partial computable, in place of `U`.

*Needs:* 1.1, 1.3, 4.1; Mathlib `Nat.bits`, `Nat.bits_append_bit`, `Nat.size_eq_bits_len`,
`Nat.size_le`, `Nat.lt_pow_succ_log_self`, `Nat.log_mono_right`.

### Examples

- With 1.3(a), 4.4(b) gives `K(x) ≤ |x| + 2 log₂ |x| + c` for some `c`, while 4.3 excludes
  `K(x) ≤ |x| + c`.

### Dependencies

4.1 uses 1.1 and the header of 1.2; 4.2 uses 1.1; 4.3 uses 4.2; 4.4 uses 1.1, 1.3 and 4.1.

## Scope and ownership

**This roadmap owns** the complexity of strings relative to a description map, optimal and
optimal prefix-free description maps, the invariance theorems for both, the length and
transformation bounds, the counting bounds and their converse for enumerable families, upper
semicomputability, Berry's paradox with the non-computability of complexity, the simplicity of the
set of compressible strings, Kraft's inequality for complexity, the failure of the length bound
for prefix-free complexity, and the comparison of plain and prefix-free complexity.

**Mathlib** owns partial recursive functions, their codes, universal and bounded evaluation, c.e.
predicates and the halting problem, and prefix-free sets of words with Kraft's inequality; they
are used, not restated.

**Tau Ceti** owns immune and simple sets (`Set.Immune`, `Set.Simple`), which realise L5.2 of the
roadmap ComputabilityTheory; 3.3 states its conclusion in that vocabulary. ComputabilityTheory
places algorithmic randomness outside its scope, and nothing here restates its targets.

**Not treated:** conditional complexity and symmetry of information, complexity of pairs,
a priori probability and the coding theorem, monotone complexity, Martin-Löf randomness and
Chaitin's number, and Chaitin's incompleteness theorem, which needs formal theories of arithmetic.

**Prior formalisation.** A. Milovanov's Lean 4 library *kolmogorov-complexity-lean* (Apache-2.0,
[Milovanov] below), built on Mathlib's partial recursive functions, reports in its README that it
formalises essentially the whole of [SUV], and its coverage table lists Theorems 1, 2, 3, 5, 7, 8,
10, 49 and 57 of [SUV], the sources of most targets here, as proved. This roadmap is an independent
specification of the mathematics, not a port: no declaration, statement or proof is taken from that
library, nothing here depends on it, and the definitions here have their own form. The notions
correspond as follows: complexity there is defined for conditional maps on pairs (program,
condition), and its plain complexity for a map `M` is the complexity here of `p ↦ M (p, [])`; if
`M` is optimal there, this map is optimal here, since every description map here, made to ignore
the condition, is a conditional map. Reusing its code in Tau Ceti would be a matter for
coordination with its author.

## Exact supplier contracts

### From Mathlib

- `Mathlib/Computability/PartrecCode.lean`: `Nat.Partrec.Code` with its `Denumerable` instance;
  `Nat.Partrec.Code.eval : Code → ℕ →. ℕ`; `Nat.Partrec.Code.eval_part : Partrec₂ eval`;
  `Nat.Partrec.Code.exists_code : Nat.Partrec f ↔ ∃ c, eval c = f`;
  `Nat.Partrec.Code.evaln : ℕ → Code → ℕ → Option ℕ`; `Nat.Partrec.Code.evaln_bound`
  (`x ∈ evaln k c n → n < k`); `Nat.Partrec.Code.evaln_mono`; `Nat.Partrec.Code.evaln_sound`;
  `Nat.Partrec.Code.evaln_complete` (`x ∈ eval c n ↔ ∃ k, x ∈ evaln k c n`);
  `Nat.Partrec.Code.primrec_evaln`.
- `Mathlib/Computability/Partrec.lean`: `Partrec`, `Computable`, `Partrec.bind`, `Partrec.comp`
  (with a computable inner map), `Partrec.rfind`, `Computable.partrec`;
  `Mathlib/Computability/Primrec/Basic.lean`: `Primrec.ofNat`, `Primrec.decode`.
- `Mathlib/Computability/RE.lean` and `Halting.lean`: `REPred`, `Partrec.dom_re` (the domain of a
  partial computable function is c.e.), `ComputablePred.halting_problem_not_re`
  (`¬REPred fun c => ¬(eval c n).Dom`).
- `Mathlib/InformationTheory/Coding/PrefixFree.lean` and `Kraft.lean`:
  `InformationTheory.IsPrefixFree`, `InformationTheory.IsPrefixFree.anti`,
  `InformationTheory.IsPrefixFree.summable_one_div_card_pow_length` and
  `InformationTheory.IsPrefixFree.tsum_one_div_card_pow_length_le_one` (for a finite nonempty
  alphabet `α` and a prefix-free `S`, `∑' w : S, (1 / card α) ^ |w| ≤ 1`).
- `Mathlib/Data/Nat/Bits.lean`, `Size.lean`, `Mathlib/Data/Nat/Log.lean`: `Nat.bits`,
  `Nat.bits_append_bit` (`(bit b n).bits = b :: n.bits` when `n = 0 → b = true`),
  `Nat.size_eq_bits_len`, `Nat.size_le` (`size m ≤ n ↔ m < 2 ^ n`), `Nat.lt_pow_succ_log_self`
  (for `1 < b`), `Nat.log_mono_right`.
- Order and sums: `iInf_lt_iff` (complete linear orders), `Part.mem_unique`, `Encodable.encodek`,
  `Equiv.tsum_eq`, `ENNReal.ofReal_tsum_of_nonneg` (nonnegative summable families),
  `ENNReal.ofReal_pow` (nonnegative base),
  `sum_le_tsum`, `Fintype.card_bool`, `Set.encard`, `List.IsPrefix`.

### From Tau Ceti

- `TauCeti/Computability/Simple/Basic.lean`: `Set.Immune X` for `[Primcodable α]` (`X` infinite
  with no infinite c.e. subset) and `Set.Simple A` (`A` c.e. with immune complement), realising
  L5.2 of ComputabilityTheory.

## References

- **[SUV]** A. Shen, V. A. Uspensky, N. Vereshchagin, *Kolmogorov Complexity and Algorithmic
  Randomness*, Mathematical Surveys and Monographs 220, American Mathematical Society, 2017.
  Locators are theorem numbers and printed page numbers of the authors' draft of September 2016,
  https://www.lirmm.fr/~ashen/kolmbook-eng.pdf. Theorems 1–6 are in the introductory chapter
  "What is this book about?", Theorems 7–10 in Chapter 1, Theorems 49 and 57 in Chapter 4.
- **[Milovanov]** A. Milovanov, *kolmogorov-complexity-lean*, a Lean 4 library of algorithmic
  information theory on Mathlib (Apache-2.0), README and coverage table `docs/SUV_COVERAGE.md` at
  commit `77b47ac7d3cac1787f9bfcb05256758e1be8cc5c`,
  https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean. Cited as prior work only (Scope
  and ownership).
