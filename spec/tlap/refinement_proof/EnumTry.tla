------------------------------ MODULE EnumTry ------------------------------
EXTENDS Integers, Sequences, FiniteSets, NaturalsInduction,
        SequenceTheorems, FiniteSetTheorems, TLAPS

LEMMA Ax ==
    ASSUME NEW P(_), NEW c, P(c)
    PROVE  P(CHOOSE x : P(x))
PROOF
    BY Zenon

LEMMA HasFresh ==
    ASSUME NEW S, IsFiniteSet(S), NEW R, IsFiniteSet(R),
           R \subseteq S, Cardinality(R) < Cardinality(S)
    PROVE  \E y \in S : y \notin R
PROOF
    <1>1. R \in SUBSET S
        OBVIOUS
    <1>2. Cardinality(R) = Cardinality(S) => R = S
        BY <1>1, FS_Subset
    <1>3. Cardinality(R) \in Nat /\ Cardinality(S) \in Nat
        BY FS_CardinalityType
    <1>4. Cardinality(R) /= Cardinality(S)
        BY <1>3, Z3
    <1>5. R /= S
        BY <1>2, <1>4, Zenon
    <1>6. QED
        BY <1>5, Zenon

LEMMA InjCard ==
    ASSUME NEW E, NEW seq \in Seq(E), IsInjective(seq)
    PROVE  IsFiniteSet(Range(seq)) /\ Cardinality(Range(seq)) = Len(seq)
PROOF
    <1>1. /\ Len(seq) \in Nat
          /\ DOMAIN seq = 1 .. Len(seq)
          /\ seq \in [1 .. Len(seq) -> E]
        BY LenProperties
    <1>2. /\ IsFiniteSet(1 .. Len(seq))
          /\ Cardinality(1 .. Len(seq)) = Len(seq)
        BY <1>1, FS_Interval, Z3
    <1>3. seq \in [1 .. Len(seq) -> Range(seq)]
        BY <1>1, Zenon DEF Range
    <1>4. seq \in Surjection(1 .. Len(seq), Range(seq))
        BY <1>1, <1>3, Zenon DEF Surjection, Range
    <1>5. seq \in Injection(1 .. Len(seq), Range(seq))
        BY <1>1, <1>3, Zenon DEF Injection, IsInjective
    <1>6. IsFiniteSet(Range(seq)) /\ Cardinality(Range(seq)) = Len(seq)
        BY <1>2, <1>4, <1>5, FS_Surjection
    <1>7. QED
        BY <1>6

LEMMA NotInRange ==
    ASSUME NEW E, NEW pre \in Seq(E), NEW y,
           \A i \in 1 .. Len(pre) : pre[i] /= y
    PROVE  y \notin Range(pre)
PROOF
    <1>1. DOMAIN pre = 1 .. Len(pre)
        BY LenProperties
    <1>2. QED
        BY <1>1, Zenon DEF Range

LEMMA TakeFresh ==
    ASSUME NEW S, NEW pre, NEW c,
           c \in S /\ \A i \in 1 .. Len(pre) : pre[i] /= c
    PROVE  LET y == CHOOSE z \in S : \A i \in 1 .. Len(pre) : pre[i] /= z
           IN  y \in S /\ \A i \in 1 .. Len(pre) : pre[i] /= y
PROOF
    <1> DEFINE R(z) == z \in S /\ \A i \in 1 .. Len(pre) : pre[i] /= z
    <1>1. R(c)
        BY DEF R
    <1>2. R(CHOOSE z : R(z))
        BY <1>1, Ax DEF R
    <1>3. (CHOOSE z \in S : \A i \in 1 .. Len(pre) : pre[i] /= z)
            = (CHOOSE z : R(z))
        BY Zenon DEF R
    <1>4. QED
        BY <1>2, <1>3 DEF R

LEMMA AppendFresh ==
    ASSUME NEW E, NEW pre \in Seq(E), IsInjective(pre),
           NEW y \in E, y \notin Range(pre)
    PROVE  Append(pre, y) \in Seq(E)
            /\ IsInjective(Append(pre, y))
            /\ Len(Append(pre, y)) = Len(pre) + 1
            /\ Range(Append(pre, y)) = Range(pre) \cup {y}
PROOF
    <1>1. Append(pre, y) \in Seq(E)
        BY AppendProperties
    <1>2. Len(Append(pre, y)) = Len(pre) + 1
        BY AppendProperties
    <1>3. Range(Append(pre, y)) = Range(pre) \cup {y}
        BY AppendProperties
    <1>4. IsInjective(Append(pre, y))
        BY AppendInjectiveSeq
    <1>5. QED
        BY <1>1, <1>2, <1>3, <1>4, Zenon

LEMMA OutOfRange ==
    ASSUME NEW E, NEW pre \in Seq(E), NEW y, y \notin Range(pre)
    PROVE  \A i \in 1 .. Len(pre) : pre[i] /= y
PROOF
    <1>1. DOMAIN pre = 1 .. Len(pre)
        BY LenProperties
    <1>2. QED
        BY <1>1, Zenon DEF Range

LEMMA CardAdd ==
    ASSUME NEW S, IsFiniteSet(S), NEW y, y \notin S
    PROVE  IsFiniteSet(S \cup {y}) /\ Cardinality(S \cup {y}) = Cardinality(S) + 1
PROOF
    <1>1. IsFiniteSet(S \cup {y})
          /\ Cardinality(S \cup {y})
               = IF y \in S THEN Cardinality(S) ELSE Cardinality(S) + 1
        BY FS_AddElement
    <1>2. QED
        BY <1>1, Z3

LEMMA OneMore ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW pre \in Seq(S), IsInjective(pre),
           Range(pre) \subseteq S,
           IsFiniteSet(Range(pre)),
           Cardinality(Range(pre)) = Len(pre),
           Len(pre) < Cardinality(S)
    PROVE  LET y == CHOOSE z \in S : \A i \in 1 .. Len(pre) : pre[i] /= z
                nxt == pre \o << y >>
            IN  /\ nxt \in Seq(S)
                /\ IsInjective(nxt)
                /\ Len(nxt) = Len(pre) + 1
                /\ Range(nxt) \subseteq S
                /\ IsFiniteSet(Range(nxt))
                /\ Cardinality(Range(nxt)) = Len(nxt)
PROOF
    <1>1. \E c \in S : c \notin Range(pre)
        BY HasFresh
    <1>2. PICK c \in S : c \notin Range(pre)
        BY <1>1
    <1>3. \A i \in 1 .. Len(pre) : pre[i] /= c
        BY <1>2, OutOfRange
    <1> DEFINE y == CHOOSE z \in S : \A i \in 1 .. Len(pre) : pre[i] /= z
    <1>4. y \in S /\ \A i \in 1 .. Len(pre) : pre[i] /= y
        BY <1>3, TakeFresh DEF y
    <1>4b. y \in S
        BY <1>4, Zenon
    <1>5. y \notin Range(pre)
        BY <1>4, NotInRange
    <1>6. /\ Append(pre, y) \in Seq(S)
          /\ IsInjective(Append(pre, y))
          /\ Len(Append(pre, y)) = Len(pre) + 1
          /\ Range(Append(pre, y)) = Range(pre) \cup {y}
        BY <1>4, <1>5, AppendFresh
    <1>7. Append(pre, y) = pre \o << y >>
        BY <1>4b, AppendIsConcat
    <1>8. IsFiniteSet(Range(pre) \cup {y})
          /\ Cardinality(Range(pre) \cup {y}) = Cardinality(Range(pre)) + 1
        BY <1>5, CardAdd
    <1>9. Range(pre) \cup {y} \subseteq S
        BY <1>4, Zenon
    <1>10. QED
        BY <1>6, <1>7, <1>8, <1>9, Zenon DEF y

LEMMA IfStep ==
    ASSUME NEW Go(_), NEW v, NEW n \in Nat, NEW m \in 1 .. n
    PROVE  (IF m = 0 THEN << >> ELSE Go(v[m - 1])) = Go(v[m - 1])
PROOF
    BY Z3

LEMMA ReadFold ==
    ASSUME NEW S, NEW n \in Nat, NEW u,
           u = [k \in 0 .. n |->
                  IF k = 0 THEN << >>
                  ELSE u[k - 1] \o << CHOOSE y \in S :
                         \A i \in 1 .. Len(u[k - 1]) : u[k - 1][i] /= y >> ]
    PROVE  /\ u[0] = << >>
            /\ \A m \in 1 .. n :
                  u[m] = u[m - 1] \o << CHOOSE y \in S :
                           \A i \in 1 .. Len(u[m - 1]) : u[m - 1][i] /= y >>
PROOF
    <1> DEFINE pick(pre) ==
            CHOOSE y \in S : \A i \in 1 .. Len(pre) : pre[i] /= y
    <1> DEFINE step(pre) == pre \o << pick(pre) >>
    <1> DEFINE h(k) == IF k = 0 THEN << >> ELSE step(u[k - 1])
    <1>1. u = [k \in 0 .. n |-> h(k)]
        BY Zenon DEF h, step, pick
    <1>2. \A m \in 0 .. n : u[m] = h(m)
        <2> HIDE DEF h, step, pick
        <2>1. QED
            BY <1>1, Isa
    <1>2b. ASSUME NEW m \in 1 .. n
           PROVE  u[m] = h(m)
        <2>1. m \in 0 .. n
            BY Z3
        <2> HIDE DEF h, step, pick
        <2>2. QED
            BY <1>1, <2>1, Isa
    <1>3. u[0] = << >>
        BY Z3
    <1>4. ASSUME NEW m \in 1 .. n
          PROVE  (IF m = 0 THEN << >> ELSE step(u[m - 1])) = step(u[m - 1])
        <2> HIDE DEF step, pick, h
        <2>1. QED
            BY ONLY IfStep, Isa
    <1>4b. ASSUME NEW m \in 1 .. n
           PROVE  h(m) = (IF m = 0 THEN << >> ELSE step(u[m - 1]))
        BY Zenon DEF h
    <1>4c. ASSUME NEW m \in 1 .. n
           PROVE  h(m) = step(u[m - 1])
        BY <1>4, <1>4b, Zenon
    <1>5. ASSUME NEW m \in 1 .. n
          PROVE  u[m] = step(u[m - 1])
        BY <1>2b, <1>4c, Zenon
    <1>6. ASSUME NEW m \in 1 .. n
          PROVE  u[m] = u[m - 1] \o << CHOOSE y \in S :
                           \A i \in 1 .. Len(u[m - 1]) : u[m - 1][i] /= y >>
        BY <1>5, Zenon DEF step, pick
    <1>7. \A m \in 1 .. n :
             u[m] = u[m - 1] \o << CHOOSE y \in S :
                      \A i \in 1 .. Len(u[m - 1]) : u[m - 1][i] /= y >>
        BY <1>6
    <1>8. QED
        BY <1>3, <1>7, Zenon

LEMMA EmptyGood ==
    ASSUME NEW S
    PROVE  /\ << >> \in Seq(S)
           /\ IsInjective(<< >>)
           /\ Len(<< >>) = 0
           /\ Range(<< >>) \subseteq S
           /\ IsFiniteSet(Range(<< >>))
           /\ Cardinality(Range(<< >>)) = 0
PROOF
    <1>1. << >> \in Seq(S) /\ Len(<< >>) = 0
        BY EmptySeq
    <1>2. IsInjective(<< >>)
        BY EmptySingletonIsInjective
    <1>3. Range(<< >>) = {}
        BY SMT DEF Range
    <1>4. IsFiniteSet({}) /\ Cardinality({}) = 0
        BY FS_EmptySet
    <1>5. QED
        BY <1>1, <1>2, <1>3, <1>4, Zenon

LEMMA StepGood ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW n \in Nat, n = Cardinality(S),
           NEW seq \in Seq(S), IsInjective(seq),
           Range(seq) \subseteq S,
           IsFiniteSet(Range(seq)),
           Cardinality(Range(seq)) = Len(seq),
           Len(seq) \in Nat, Len(seq) < n,
           NEW out,
           out = seq \o << CHOOSE y \in S :
                    \A i \in 1 .. Len(seq) : seq[i] /= y >>
    PROVE  /\ out \in Seq(S)
           /\ IsInjective(out)
           /\ Len(out) = Len(seq) + 1
           /\ Range(out) \subseteq S
           /\ IsFiniteSet(Range(out))
           /\ Cardinality(Range(out)) = Len(out)
PROOF
    <1>1. Len(seq) < Cardinality(S)
        BY Z3
    <1>2. LET y == CHOOSE z \in S : \A i \in 1 .. Len(seq) : seq[i] /= z
              w == seq \o << y >>
          IN  /\ w \in Seq(S)
              /\ IsInjective(w)
              /\ Len(w) = Len(seq) + 1
              /\ Range(w) \subseteq S
              /\ IsFiniteSet(Range(w))
              /\ Cardinality(Range(w)) = Len(w)
        BY <1>1, OneMore
    <1>3. LET y == CHOOSE z \in S : \A i \in 1 .. Len(seq) : seq[i] /= z
              w == seq \o << y >>
          IN  w = out
        BY Zenon
    <1>4. QED
        BY <1>2, <1>3, Zenon

LEMMA InDown ==
    ASSUME NEW n \in Nat, NEW j \in Nat, j + 1 \in 0 .. n
    PROVE  /\ j \in 0 .. n
           /\ j + 1 \in 1 .. n
           /\ j < n
PROOF
    BY Z3

LEMMA BaseInv ==
    ASSUME NEW S, NEW u, u[0] = << >>
    PROVE  /\ u[0] \in Seq(S)
           /\ IsInjective(u[0])
           /\ Len(u[0]) = 0
           /\ Range(u[0]) \subseteq S
           /\ IsFiniteSet(Range(u[0]))
           /\ Cardinality(Range(u[0])) = 0
PROOF
    BY EmptyGood, Zenon

LEMMA UseAt ==
    ASSUME NEW S, NEW n \in Nat, NEW u, NEW m \in 1 .. n,
           \A i \in 1 .. n :
              u[i] = u[i - 1] \o << CHOOSE y \in S :
                       \A t \in 1 .. Len(u[i - 1]) : u[i - 1][t] /= y >>
    PROVE  u[m] = u[m - 1] \o << CHOOSE y \in S :
                     \A t \in 1 .. Len(u[m - 1]) : u[m - 1][t] /= y >>
PROOF
    BY Zenon

LEMMA OpenInv ==
    ASSUME NEW n \in Nat, NEW j \in Nat, NEW u, NEW S,
           j + 1 \in 0 .. n,
           j \in 0 .. n =>
              /\ u[j] \in Seq(S)
              /\ IsInjective(u[j])
              /\ Len(u[j]) = j
              /\ Range(u[j]) \subseteq S
              /\ IsFiniteSet(Range(u[j]))
              /\ Cardinality(Range(u[j])) = j
    PROVE  /\ u[j] \in Seq(S)
           /\ IsInjective(u[j])
           /\ Len(u[j]) = j
           /\ Range(u[j]) \subseteq S
           /\ IsFiniteSet(Range(u[j]))
           /\ Cardinality(Range(u[j])) = j
PROOF
    <1>1. j \in 0 .. n
        BY InDown
    <1>2. QED
        BY <1>1, Zenon

LEMMA Prep ==
    ASSUME NEW n \in Nat, NEW j \in Nat, NEW S, NEW u,
           j \in 0 .. n =>
              /\ u[j] \in Seq(S)
              /\ IsInjective(u[j])
              /\ Len(u[j]) = j
              /\ Range(u[j]) \subseteq S
              /\ IsFiniteSet(Range(u[j]))
              /\ Cardinality(Range(u[j])) = j
    PROVE  j + 1 \in 0 .. n =>
              /\ j + 1 \in 1 .. n
              /\ u[j] \in Seq(S)
              /\ IsInjective(u[j])
              /\ Len(u[j]) = j
              /\ Range(u[j]) \subseteq S
              /\ IsFiniteSet(Range(u[j]))
              /\ Cardinality(Range(u[j])) = j
              /\ Len(u[j]) \in Nat
              /\ Len(u[j]) < n
PROOF
    <1>1. j + 1 \in 0 .. n => j \in 0 .. n /\ j + 1 \in 1 .. n /\ j < n
        BY InDown
    <1>2. j + 1 \in 0 .. n =>
             /\ u[j] \in Seq(S)
             /\ IsInjective(u[j])
             /\ Len(u[j]) = j
             /\ Range(u[j]) \subseteq S
             /\ IsFiniteSet(Range(u[j]))
             /\ Cardinality(Range(u[j])) = j
        BY <1>1, Zenon
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA UseAtSucc ==
    ASSUME NEW S, NEW n \in Nat, NEW u, NEW j \in Nat,
           j + 1 \in 1 .. n,
           \A m \in 1 .. n :
              u[m] = u[m - 1] \o << CHOOSE y \in S :
                       \A t \in 1 .. Len(u[m - 1]) : u[m - 1][t] /= y >>
    PROVE  u[j + 1] = u[(j + 1) - 1] \o << CHOOSE y \in S :
                         \A t \in 1 .. Len(u[(j + 1) - 1]) : u[(j + 1) - 1][t] /= y >>
PROOF
    BY UseAt

LEMMA UseImp ==
    ASSUME NEW S, NEW n \in Nat, NEW u, NEW j \in Nat,
           \A m \in 1 .. n :
              u[m] = u[m - 1] \o << CHOOSE y \in S :
                       \A t \in 1 .. Len(u[m - 1]) : u[m - 1][t] /= y >>
    PROVE  j + 1 \in 1 .. n =>
              u[j + 1] = u[j] \o << CHOOSE y \in S :
                           \A t \in 1 .. Len(u[j]) : u[j][t] /= y >>
PROOF
    <1>1. ASSUME NEW c \in {j + 1} \cap (1 .. n)
          PROVE  u[j + 1] = u[j] \o << CHOOSE y \in S :
                                \A t \in 1 .. Len(u[j]) : u[j][t] /= y >>
        <2>1. c = j + 1 /\ j + 1 \in 1 .. n
            BY Z3
        <2>2. u[j + 1] = u[(j + 1) - 1] \o << CHOOSE y \in S :
                             \A t \in 1 .. Len(u[(j + 1) - 1]) :
                               u[(j + 1) - 1][t] /= y >>
            BY <2>1, UseAtSucc
        <2>3. QED
            BY <2>2, Z3
    <1>2. QED
        BY <1>1, Zenon

LEMMA ApplyFlat ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW n \in Nat, n = Cardinality(S),
           NEW pre \in Seq(S), IsInjective(pre),
           Range(pre) \subseteq S,
           IsFiniteSet(Range(pre)),
           Cardinality(Range(pre)) = Len(pre),
           Len(pre) \in Nat, Len(pre) < n,
           NEW nxt,
           nxt = pre \o << CHOOSE y \in S :
                    \A i \in 1 .. Len(pre) : pre[i] /= y >>
    PROVE  /\ nxt \in Seq(S)
           /\ IsInjective(nxt)
           /\ Len(nxt) = Len(pre) + 1
           /\ Range(nxt) \subseteq S
           /\ IsFiniteSet(Range(nxt))
           /\ Cardinality(Range(nxt)) = Len(nxt)
PROOF
    <1>1. Len(pre) < Cardinality(S)
        BY Z3
    <1>2. LET y == CHOOSE z \in S : \A i \in 1 .. Len(pre) : pre[i] /= z
              w == pre \o << y >>
          IN  /\ w \in Seq(S)
              /\ IsInjective(w)
              /\ Len(w) = Len(pre) + 1
              /\ Range(w) \subseteq S
              /\ IsFiniteSet(Range(w))
              /\ Cardinality(Range(w)) = Len(w)
        BY <1>1, OneMore
    <1>3. LET y == CHOOSE z \in S : \A i \in 1 .. Len(pre) : pre[i] /= z
              w == pre \o << y >>
          IN  w = nxt
        BY Zenon
    <1>4. QED
        BY <1>2, <1>3, Zenon

LEMMA ApplyWithRec ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW n \in Nat, n = Cardinality(S),
           NEW pre \in Seq(S), IsInjective(pre),
           Range(pre) \subseteq S,
           IsFiniteSet(Range(pre)),
           Cardinality(Range(pre)) = Len(pre),
           Len(pre) \in Nat, Len(pre) < n,
           NEW nxt,
           nxt = pre \o << CHOOSE y \in S :
                    \A i \in 1 .. Len(pre) : pre[i] /= y >>,
           NEW u, NEW m \in Nat,
           \A q \in 1 .. m :
              u[q] = u[q - 1] \o << CHOOSE y \in S :
                       \A t \in 1 .. Len(u[q - 1]) : u[q - 1][t] /= y >>
    PROVE  /\ nxt \in Seq(S)
           /\ IsInjective(nxt)
           /\ Len(nxt) = Len(pre) + 1
           /\ Range(nxt) \subseteq S
           /\ IsFiniteSet(Range(nxt))
           /\ Cardinality(Range(nxt)) = Len(nxt)
PROOF
    <1>1. Len(pre) < Cardinality(S)
        BY Z3
    <1>2. LET y == CHOOSE z \in S : \A i \in 1 .. Len(pre) : pre[i] /= z
              w == pre \o << y >>
          IN  /\ w \in Seq(S)
              /\ IsInjective(w)
              /\ Len(w) = Len(pre) + 1
              /\ Range(w) \subseteq S
              /\ IsFiniteSet(Range(w))
              /\ Cardinality(Range(w)) = Len(w)
        BY <1>1, OneMore
    <1>3. LET y == CHOOSE z \in S : \A i \in 1 .. Len(pre) : pre[i] /= z
              w == pre \o << y >>
          IN  w = nxt
        BY Zenon
    <1>4. QED
        BY <1>2, <1>3, Zenon

LEMMA SubstFun ==
    ASSUME NEW u, NEW j \in Nat, (j + 1) - 1 = j
    PROVE  u[(j + 1) - 1] = u[j]
PROOF
    BY Zenon

LEMMA SubstFunZ ==
    ASSUME NEW u, NEW j \in Nat, (j + 1) - 1 = j
    PROVE  u[(j + 1) - 1] = u[j]
PROOF
    BY Z3

LEMMA SubstFunI ==
    ASSUME NEW u, NEW j \in Nat, (j + 1) - 1 = j
    PROVE  u[(j + 1) - 1] = u[j]
PROOF
    BY Isa

LEMMA SubstSeq ==
    ASSUME NEW S, NEW u, NEW j \in Nat, (j + 1) - 1 = j,
           u[j + 1] = u[(j + 1) - 1] \o << CHOOSE y \in S :
                         \A t \in 1 .. Len(u[(j + 1) - 1]) :
                           u[(j + 1) - 1][t] /= y >>
    PROVE  u[j + 1] = u[j] \o << CHOOSE y \in S :
                         \A t \in 1 .. Len(u[j]) : u[j][t] /= y >>
PROOF
    BY Zenon

LEMMA ArithN ==
    ASSUME NEW j \in Nat
    PROVE  (j + 1) - 1 = j
PROOF
    BY Z3

LEMMA ReindexFromRec ==
    ASSUME NEW S, NEW n \in Nat, NEW u, NEW j \in Nat,
           j + 1 \in 1 .. n,
           \A m \in 1 .. n :
              u[m] = u[m - 1] \o << CHOOSE y \in S :
                       \A t \in 1 .. Len(u[m - 1]) : u[m - 1][t] /= y >>
    PROVE  u[j + 1] = u[j] \o << CHOOSE y \in S :
                         \A t \in 1 .. Len(u[j]) : u[j][t] /= y >>
PROOF
    <1>1. (j + 1) - 1 = j
        BY ArithN
    <1>2. u[j + 1] = u[(j + 1) - 1] \o << CHOOSE y \in S :
                        \A t \in 1 .. Len(u[(j + 1) - 1]) :
                          u[(j + 1) - 1][t] /= y >>
        BY UseAtSucc
    <1>3. QED
        BY <1>1, <1>2, SubstSeq

LEMMA StepAt ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW n \in Nat, n = Cardinality(S),
           NEW u, NEW j \in Nat,
           j + 1 \in 1 .. n,
           u[j] \in Seq(S),
           IsInjective(u[j]),
           Range(u[j]) \subseteq S,
           IsFiniteSet(Range(u[j])),
           Cardinality(Range(u[j])) = Len(u[j]),
           Len(u[j]) \in Nat,
           Len(u[j]) < n,
           \A m \in 1 .. n :
              u[m] = u[m - 1] \o << CHOOSE y \in S :
                       \A t \in 1 .. Len(u[m - 1]) : u[m - 1][t] /= y >>
    PROVE  /\ u[j + 1] \in Seq(S)
           /\ IsInjective(u[j + 1])
           /\ Len(u[j + 1]) = Len(u[j]) + 1
           /\ Range(u[j + 1]) \subseteq S
           /\ IsFiniteSet(Range(u[j + 1]))
           /\ Cardinality(Range(u[j + 1])) = Len(u[j + 1])
PROOF
    <1>1. (j + 1) - 1 = j
        BY ArithN
    <1>2. u[j + 1] = u[j] \o << CHOOSE y \in S :
                        \A t \in 1 .. Len(u[j]) : u[j][t] /= y >>
        BY ReindexFromRec
    <1>2b. u[j + 1] = u[j] \o << CHOOSE y \in S :
                         \A i \in 1 .. Len(u[j]) : u[j][i] /= y >>
        BY <1>2, Zenon
    <1>3. Len(u[j]) < Cardinality(S)
        BY Z3
    <1>4. LET y == CHOOSE z \in S : \A i \in 1 .. Len(u[j]) : u[j][i] /= z
              w == u[j] \o << y >>
          IN  /\ w \in Seq(S)
              /\ IsInjective(w)
              /\ Len(w) = Len(u[j]) + 1
              /\ Range(w) \subseteq S
              /\ IsFiniteSet(Range(w))
              /\ Cardinality(Range(w)) = Len(w)
        BY <1>3, OneMore
    <1>5. LET y == CHOOSE z \in S : \A i \in 1 .. Len(u[j]) : u[j][i] /= z
              w == u[j] \o << y >>
          IN  w = u[j + 1]
        BY <1>2b, Zenon
    <1>6. QED
        BY <1>4, <1>5, Zenon

LEMMA InOne ==
    ASSUME NEW n \in Nat, NEW j \in Nat, j + 1 \in 0 .. n
    PROVE  j + 1 \in 1 .. n
PROOF
    BY Z3

LEMMA Jlt ==
    ASSUME NEW n \in Nat, NEW j \in Nat, j + 1 \in 0 .. n
    PROVE  j < n
PROOF
    BY Z3

LEMMA LenNat ==
    ASSUME NEW pre, NEW j \in Nat, Len(pre) = j
    PROVE  Len(pre) \in Nat
PROOF
    BY Z3

LEMMA LenLt ==
    ASSUME NEW pre, NEW j \in Nat, NEW n \in Nat, Len(pre) = j, j < n
    PROVE  Len(pre) < n
PROOF
    BY Z3

LEMMA CardLen ==
    ASSUME NEW R, NEW pre, NEW j \in Nat,
           Cardinality(R) = j, Len(pre) = j
    PROVE  Cardinality(R) = Len(pre)
PROOF
    BY Z3

LEMMA Add1 ==
    ASSUME NEW a \in Nat, NEW b, NEW j \in Nat, a = j, b = a + 1
    PROVE  b = j + 1
PROOF
    BY Z3

LEMMA RunStep ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW n \in Nat, n = Cardinality(S),
           NEW u, NEW j \in Nat,
           j + 1 \in 1 .. n,
           j < n,
           /\ u[j] \in Seq(S)
           /\ IsInjective(u[j])
           /\ Len(u[j]) = j
           /\ Range(u[j]) \subseteq S
           /\ IsFiniteSet(Range(u[j]))
           /\ Cardinality(Range(u[j])) = j,
           \A m \in 1 .. n :
              u[m] = u[m - 1] \o << CHOOSE y \in S :
                       \A t \in 1 .. Len(u[m - 1]) : u[m - 1][t] /= y >>
    PROVE  /\ u[j + 1] \in Seq(S)
           /\ IsInjective(u[j + 1])
           /\ Len(u[j + 1]) = Len(u[j]) + 1
           /\ Range(u[j + 1]) \subseteq S
           /\ IsFiniteSet(Range(u[j + 1]))
           /\ Cardinality(Range(u[j + 1])) = Len(u[j + 1])
PROOF
    <1>1. u[j] \in Seq(S)
        BY Zenon
    <1>2. IsInjective(u[j])
        BY Zenon
    <1>3. Len(u[j]) = j
        BY Zenon
    <1>4. Range(u[j]) \subseteq S
        BY Zenon
    <1>5. IsFiniteSet(Range(u[j]))
        BY Zenon
    <1>6. Cardinality(Range(u[j])) = j
        BY Zenon
    <1>7. Len(u[j]) \in Nat
        BY <1>3, LenNat
    <1>8. Len(u[j]) < n
        BY <1>3, LenLt
    <1>9. Cardinality(Range(u[j])) = Len(u[j])
        BY <1>3, <1>6, CardLen
    <1>10. QED
        BY <1>1, <1>2, <1>4, <1>5, <1>7, <1>8, <1>9, StepAt

LEMMA LenPlus ==
    ASSUME NEW S, NEW u, NEW j \in Nat,
           /\ u[j] \in Seq(S)
           /\ IsInjective(u[j])
           /\ Len(u[j]) = j
           /\ Range(u[j]) \subseteq S
           /\ IsFiniteSet(Range(u[j]))
           /\ Cardinality(Range(u[j])) = j,
           /\ u[j + 1] \in Seq(S)
           /\ IsInjective(u[j + 1])
           /\ Len(u[j + 1]) = Len(u[j]) + 1
           /\ Range(u[j + 1]) \subseteq S
           /\ IsFiniteSet(Range(u[j + 1]))
           /\ Cardinality(Range(u[j + 1])) = Len(u[j + 1])
    PROVE  Len(u[j + 1]) = j + 1
PROOF
    <1>1. Len(u[j]) = j
        BY Zenon
    <1>2. Len(u[j + 1]) = Len(u[j]) + 1
        BY Zenon
    <1>3. Len(u[j]) \in Nat
        BY <1>1, LenNat
    <1>4. QED
        BY <1>1, <1>2, <1>3, Add1

LEMMA CardPlus ==
    ASSUME NEW S, NEW u, NEW j \in Nat,
           /\ u[j + 1] \in Seq(S)
           /\ IsInjective(u[j + 1])
           /\ Len(u[j + 1]) = Len(u[j]) + 1
           /\ Range(u[j + 1]) \subseteq S
           /\ IsFiniteSet(Range(u[j + 1]))
           /\ Cardinality(Range(u[j + 1])) = Len(u[j + 1]),
           Len(u[j + 1]) = j + 1
    PROVE  Cardinality(Range(u[j + 1])) = j + 1
PROOF
    BY Zenon

LEMMA Pack ==
    ASSUME NEW S, NEW u, NEW j \in Nat,
           /\ u[j + 1] \in Seq(S)
           /\ IsInjective(u[j + 1])
           /\ Len(u[j + 1]) = Len(u[j]) + 1
           /\ Range(u[j + 1]) \subseteq S
           /\ IsFiniteSet(Range(u[j + 1]))
           /\ Cardinality(Range(u[j + 1])) = Len(u[j + 1]),
           Len(u[j + 1]) = j + 1,
           Cardinality(Range(u[j + 1])) = j + 1
    PROVE  /\ u[j + 1] \in Seq(S)
           /\ IsInjective(u[j + 1])
           /\ Len(u[j + 1]) = j + 1
           /\ Range(u[j + 1]) \subseteq S
           /\ IsFiniteSet(Range(u[j + 1]))
           /\ Cardinality(Range(u[j + 1])) = j + 1
PROOF
    BY Zenon

Pre(u, S, n, j) ==
    j \in 0 .. n =>
        /\ u[j] \in Seq(S)
        /\ IsInjective(u[j])
        /\ Len(u[j]) = j
        /\ Range(u[j]) \subseteq S
        /\ IsFiniteSet(Range(u[j]))
        /\ Cardinality(Range(u[j])) = j

LEMMA StepImp ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW n \in Nat, n = Cardinality(S),
           NEW u,
           \A m \in 1 .. n :
              u[m] = u[m - 1] \o << CHOOSE y \in S :
                       \A t \in 1 .. Len(u[m - 1]) : u[m - 1][t] /= y >>,
           NEW j \in Nat,
           j \in 0 .. n =>
              /\ u[j] \in Seq(S)
              /\ IsInjective(u[j])
              /\ Len(u[j]) = j
              /\ Range(u[j]) \subseteq S
              /\ IsFiniteSet(Range(u[j]))
              /\ Cardinality(Range(u[j])) = j
    PROVE  j + 1 \in 0 .. n =>
              /\ u[j + 1] \in Seq(S)
              /\ IsInjective(u[j + 1])
              /\ Len(u[j + 1]) = j + 1
              /\ Range(u[j + 1]) \subseteq S
              /\ IsFiniteSet(Range(u[j + 1]))
              /\ Cardinality(Range(u[j + 1])) = j + 1
PROOF
    <1> SUFFICES ASSUME j + 1 \in 0 .. n
                 PROVE  /\ u[j + 1] \in Seq(S)
                        /\ IsInjective(u[j + 1])
                        /\ Len(u[j + 1]) = j + 1
                        /\ Range(u[j + 1]) \subseteq S
                        /\ IsFiniteSet(Range(u[j + 1]))
                        /\ Cardinality(Range(u[j + 1])) = j + 1
        BY Zenon
    <1>1. /\ u[j] \in Seq(S)
          /\ IsInjective(u[j])
          /\ Len(u[j]) = j
          /\ Range(u[j]) \subseteq S
          /\ IsFiniteSet(Range(u[j]))
          /\ Cardinality(Range(u[j])) = j
        BY OpenInv
    <1>2. j + 1 \in 1 .. n
        BY InOne
    <1>3. j < n
        BY Jlt
    <1>4. /\ u[j + 1] \in Seq(S)
          /\ IsInjective(u[j + 1])
          /\ Len(u[j + 1]) = Len(u[j]) + 1
          /\ Range(u[j + 1]) \subseteq S
          /\ IsFiniteSet(Range(u[j + 1]))
          /\ Cardinality(Range(u[j + 1])) = Len(u[j + 1])
        BY <1>1, <1>2, <1>3, RunStep
    <1>5. Len(u[j + 1]) = j + 1
        BY <1>1, <1>4, LenPlus
    <1>6. Cardinality(Range(u[j + 1])) = j + 1
        BY <1>4, <1>5, CardPlus
    <1>7. QED
        BY <1>4, <1>5, <1>6, Pack

LEMMA StepArrow ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW n \in Nat, n = Cardinality(S),
           NEW u,
           \A m \in 1 .. n :
              u[m] = u[m - 1] \o << CHOOSE y \in S :
                       \A t \in 1 .. Len(u[m - 1]) : u[m - 1][t] /= y >>,
           NEW j \in Nat
    PROVE  Pre(u, S, n, j) => Pre(u, S, n, j + 1)
PROOF
    <1>1. ASSUME Pre(u, S, n, j)
          PROVE  Pre(u, S, n, j + 1)
        <2>1. j \in 0 .. n =>
                 /\ u[j] \in Seq(S)
                 /\ IsInjective(u[j])
                 /\ Len(u[j]) = j
                 /\ Range(u[j]) \subseteq S
                 /\ IsFiniteSet(Range(u[j]))
                 /\ Cardinality(Range(u[j])) = j
            BY Pre(u, S, n, j) DEF Pre
        <2>2. j + 1 \in 0 .. n =>
                 /\ u[j + 1] \in Seq(S)
                 /\ IsInjective(u[j + 1])
                 /\ Len(u[j + 1]) = j + 1
                 /\ Range(u[j + 1]) \subseteq S
                 /\ IsFiniteSet(Range(u[j + 1]))
                 /\ Cardinality(Range(u[j + 1])) = j + 1
            BY <2>1, StepImp
        <2>3. QED
            BY <2>2 DEF Pre
    <1>2. QED
        BY <1>1, Zenon

LEMMA InductInv ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW n \in Nat, n = Cardinality(S),
           NEW u,
           u[0] = << >>,
           \A m \in 1 .. n :
              u[m] = u[m - 1] \o << CHOOSE y \in S :
                       \A t \in 1 .. Len(u[m - 1]) : u[m - 1][t] /= y >>
    PROVE  \A k \in 0 .. n :
              /\ u[k] \in Seq(S)
              /\ IsInjective(u[k])
              /\ Len(u[k]) = k
              /\ Range(u[k]) \subseteq S
              /\ IsFiniteSet(Range(u[k]))
              /\ Cardinality(Range(u[k])) = k
PROOF
    <1>1. Pre(u, S, n, 0)
        BY BaseInv DEF Pre
    <1>2. \A j \in Nat : Pre(u, S, n, j) => Pre(u, S, n, j + 1)
        <2> SUFFICES ASSUME NEW j \in Nat
                     PROVE  Pre(u, S, n, j) => Pre(u, S, n, j + 1)
            BY Zenon
        <2>1. QED
            BY StepArrow
    <1>3. \A j \in Nat : Pre(u, S, n, j)
        BY <1>1, <1>2, NatInduction, Isa
    <1>4. QED
        BY <1>3 DEF Pre

LEMMA SameRec ==
    ASSUME NEW S, NEW n \in Nat, NEW u,
           /\ u[0] = << >>
           /\ \A m \in 1 .. n :
                 u[m] = u[m - 1] \o << CHOOSE y \in S :
                          \A i \in 1 .. Len(u[m - 1]) : u[m - 1][i] /= y >>
    PROVE  \A m \in 1 .. n :
              u[m] = u[m - 1] \o << CHOOSE y \in S :
                       \A t \in 1 .. Len(u[m - 1]) : u[m - 1][t] /= y >>
PROOF
    BY Zenon

LEMMA TakeZero ==
    ASSUME NEW S, NEW n \in Nat, NEW u,
           /\ u[0] = << >>
           /\ \A m \in 1 .. n :
                 u[m] = u[m - 1] \o << CHOOSE y \in S :
                          \A i \in 1 .. Len(u[m - 1]) : u[m - 1][i] /= y >>
    PROVE  u[0] = << >>
PROOF
    BY Zenon

LEMMA CoverAt ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW n \in Nat, n = Cardinality(S),
           NEW u,
           \A k \in 0 .. n :
              /\ u[k] \in Seq(S)
              /\ IsInjective(u[k])
              /\ Len(u[k]) = k
              /\ Range(u[k]) \subseteq S
              /\ IsFiniteSet(Range(u[k]))
              /\ Cardinality(Range(u[k])) = k
    PROVE  /\ u[n] \in Seq(S)
           /\ IsInjective(u[n])
           /\ Len(u[n]) = n
           /\ Range(u[n]) = S
PROOF
    <1>1. n \in 0 .. n
        BY Z3
    <1>2. /\ u[n] \in Seq(S)
          /\ IsInjective(u[n])
          /\ Len(u[n]) = n
          /\ Range(u[n]) \subseteq S
          /\ IsFiniteSet(Range(u[n]))
          /\ Cardinality(Range(u[n])) = n
        BY <1>1, Zenon
    <1>3. Range(u[n]) \in SUBSET S
        BY <1>2
    <1>4. Cardinality(Range(u[n])) = Cardinality(S)
        BY <1>2, Z3
    <1>5. Range(u[n]) = S
        BY <1>3, <1>4, FS_Subset
    <1>6. QED
        BY <1>2, <1>5, Zenon

LEMMA EnumSeq ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW n \in Nat, n = Cardinality(S),
           NEW u,
           u = [k \in 0 .. n |->
                  IF k = 0 THEN << >>
                  ELSE u[k - 1] \o << CHOOSE y \in S :
                         \A i \in 1 .. Len(u[k - 1]) : u[k - 1][i] /= y >> ]
    PROVE  /\ u[n] \in Seq(S)
           /\ IsInjective(u[n])
           /\ Len(u[n]) = n
           /\ Range(u[n]) = S
PROOF
    <1> DEFINE pick(pre) ==
            CHOOSE y \in S : \A i \in 1 .. Len(pre) : pre[i] /= y
    <1> DEFINE step(pre) == pre \o << pick(pre) >>
    <1> DEFINE h(k) == IF k = 0 THEN << >> ELSE step(u[k - 1])
    <1>1. u = [k \in 0 .. n |-> h(k)]
        BY Zenon DEF h, step, pick
    <1>2. \A m \in 0 .. n : u[m] = h(m)
        <2> HIDE DEF h, step, pick
        <2>1. QED
            BY <1>1, Isa
    <1>2b. ASSUME NEW m \in 1 .. n
           PROVE  u[m] = h(m)
        <2>1. m \in 0 .. n
            BY Z3
        <2> HIDE DEF h, step, pick
        <2>2. QED
            BY <1>1, <2>1, Isa
    <1>3. u[0] = << >>
        BY Z3
    <1>4. ASSUME NEW m \in 1 .. n
          PROVE  (IF m = 0 THEN << >> ELSE step(u[m - 1])) = step(u[m - 1])
        <2> HIDE DEF step, pick, h
        <2>1. QED
            BY ONLY IfStep, Isa
    <1>4b. ASSUME NEW m \in 1 .. n
           PROVE  h(m) = (IF m = 0 THEN << >> ELSE step(u[m - 1]))
        BY Zenon DEF h
    <1>4c. ASSUME NEW m \in 1 .. n
           PROVE  h(m) = step(u[m - 1])
        BY <1>4, <1>4b, Zenon
    <1>5. ASSUME NEW m \in 1 .. n
          PROVE  u[m] = step(u[m - 1])
        BY <1>2b, <1>4c, Zenon
    <1>6. ASSUME NEW m \in 1 .. n
          PROVE  u[m] = u[m - 1] \o << CHOOSE y \in S :
                           \A i \in 1 .. Len(u[m - 1]) : u[m - 1][i] /= y >>
        BY <1>5, Zenon DEF step, pick
    <1>7. \A m \in 1 .. n :
             u[m] = u[m - 1] \o << CHOOSE y \in S :
                      \A i \in 1 .. Len(u[m - 1]) : u[m - 1][i] /= y >>
        BY <1>6
    <1>8. /\ u[0] = << >>
          /\ \A m \in 1 .. n :
                u[m] = u[m - 1] \o << CHOOSE y \in S :
                         \A i \in 1 .. Len(u[m - 1]) : u[m - 1][i] /= y >>
        BY <1>3, <1>7, Zenon
    <1>9. \A m \in 1 .. n :
             u[m] = u[m - 1] \o << CHOOSE y \in S :
                      \A t \in 1 .. Len(u[m - 1]) : u[m - 1][t] /= y >>
        BY <1>8, SameRec
    <1>10. \A k \in 0 .. n :
              /\ u[k] \in Seq(S)
              /\ IsInjective(u[k])
              /\ Len(u[k]) = k
              /\ Range(u[k]) \subseteq S
              /\ IsFiniteSet(Range(u[k]))
              /\ Cardinality(Range(u[k])) = k
        BY <1>3, <1>9, InductInv
    <1>11. QED
        BY <1>10, CoverAt

=============================================================================
