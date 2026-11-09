---------------------------- MODULE FoldTry ----------------------------
EXTENDS EnumTry

LEMMA CtorEq ==
    ASSUME NEW S, NEW h(_), NEW e(_),
           \A x \in S : h(x) = e(x)
    PROVE  [x \in S |-> h(x)] = [x \in S |-> e(x)]
PROOF
    BY Zenon

LEMMA Extend ==
    ASSUME NEW Up(_, _), NEW b, NEW ms, NEW k \in Nat, NEW u,
           u = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE Up(u[n - 1], ms[n]) ]
    PROVE  LET v == [n \in 0 .. (k + 1) |->
                       IF n <= k THEN u[n]
                       ELSE Up(u[k], ms[k + 1]) ]
           IN  v = [n \in 0 .. (k + 1) |->
                      IF n = 0 THEN b
                      ELSE Up(v[n - 1], ms[n]) ]
PROOF
    <1> DEFINE v == [n \in 0 .. (k + 1) |->
                       IF n <= k THEN u[n]
                       ELSE Up(u[k], ms[k + 1]) ]
    <1> DEFINE w == [n \in 0 .. (k + 1) |->
                       IF n = 0 THEN b
                       ELSE Up(v[n - 1], ms[n]) ]
    <1> DEFINE hv(n) ==
            IF n <= k THEN u[n]
            ELSE Up(u[k], ms[k + 1])
    <1> DEFINE hw(n) ==
            IF n = 0 THEN b
            ELSE Up(v[n - 1], ms[n])
    <1>1. ASSUME NEW n \in 0 .. (k + 1)
          PROVE  hv(n) = hw(n)
        <2>0. ASSUME NEW m \in 0 .. (k + 1)
              PROVE  m \in 0 .. k => v[m] = u[m]
            BY Z3 DEF v
        <2>0b. \A m \in 0 .. (k + 1) : m \in 0 .. k => v[m] = u[m]
            BY <2>0
        <2>1. n = 0 => v[n] = w[n]
            BY Z3 DEF v, w
        <2>2. n \in 1 .. k => v[n] = u[n]
            BY Z3 DEF v
        <2>3. n \in 1 .. k => n - 1 \in 0 .. k /\ n - 1 \in 0 .. (k + 1)
            BY Z3
        <2>3b. n \in 1 .. k => v[n - 1] = u[n - 1]
            BY <2>0b, <2>3, Zenon
        <2>4. n \in 1 .. k => u[n] = Up(u[n - 1], ms[n])
            BY Z3
        <2>5. n \in 1 .. k => w[n] = Up(v[n - 1], ms[n])
            BY Z3 DEF w
        <2>6. n \in 1 .. k => v[n] = w[n]
            BY <2>2, <2>3b, <2>4, <2>5, Zenon
        <2>7. n = k + 1 => v[n] = Up(u[k], ms[k + 1])
            BY Z3 DEF v
        <2>8a. k \in 0 .. k /\ k \in 0 .. (k + 1)
            BY Z3
        <2>8. v[k] = u[k]
            BY <2>0b, <2>8a, Zenon
        <2>9. n = k + 1 => n - 1 = k
            BY Z3
        <2>10. n = k + 1 => w[n] = Up(v[k], ms[k + 1])
            BY <2>9, Z3 DEF w
        <2>11. n = k + 1 => v[n] = w[n]
            BY <2>7, <2>8, <2>10, Zenon
        <2>12. n = 0 \/ n \in 1 .. k \/ n = k + 1
            BY Z3
        <2>13. v[n] = w[n]
            BY <2>1, <2>6, <2>11, <2>12, Z3
        <2>14. hv(n) = v[n]
            BY Z3 DEF v, hv
        <2>15. hw(n) = w[n]
            BY Z3 DEF w, hw
        <2>16. QED
            BY <2>13, <2>14, <2>15, Zenon
    <1>2. \A n \in 0 .. (k + 1) : hv(n) = hw(n)
        BY <1>1
    <1>3. v = w
        <2>1. [n \in 0 .. (k + 1) |-> hv(n)] = [n \in 0 .. (k + 1) |-> hw(n)]
            BY <1>2, CtorEq DEF hv, hw
        <2>2. v = [n \in 0 .. (k + 1) |-> hv(n)]
            BY Z3 DEF v, hv
        <2>3. w = [n \in 0 .. (k + 1) |-> hw(n)]
            BY Z3 DEF w, hw
        <2>4. QED
            BY <2>1, <2>2, <2>3, Zenon
    <1>4. QED
        BY <1>3 DEF v, w

LEMMA ExistsAll ==
    ASSUME NEW Up(_, _), NEW b, NEW ms, NEW len \in Nat
    PROVE  \E u : u = [n \in 0 .. len |->
                         IF n = 0 THEN b
                         ELSE Up(u[n - 1], ms[n]) ]
PROOF
    <1> DEFINE Exists(k) ==
            \E u : u = [n \in 0 .. k |->
                          IF n = 0 THEN b
                          ELSE Up(u[n - 1], ms[n]) ]
    <1>1. Exists(0)
        <2> DEFINE f == [n \in 0 .. 0 |-> b]
        <2>1. f = [n \in 0 .. 0 |-> IF n = 0 THEN b
                                    ELSE Up(f[n - 1], ms[n]) ]
            BY Z3 DEF f
        <2>2. QED
            BY <2>1 DEF Exists
    <1>2. ASSUME NEW k \in Nat, Exists(k)
          PROVE  Exists(k + 1)
        <2> DEFINE Q(u) ==
                u = [n \in 0 .. k |->
                       IF n = 0 THEN b
                       ELSE Up(u[n - 1], ms[n]) ]
        <2>1. \E u : Q(u)
            BY <1>2 DEF Exists, Q
        <2>2. ASSUME NEW u, Q(u)
              PROVE  Exists(k + 1)
            <3> DEFINE v == [n \in 0 .. (k + 1) |->
                               IF n <= k THEN u[n]
                               ELSE Up(u[k], ms[k + 1]) ]
            <3>1. v = [n \in 0 .. (k + 1) |->
                         IF n = 0 THEN b
                         ELSE Up(v[n - 1], ms[n]) ]
                BY <1>2, <2>2, Extend DEF v, Q
            <3>2. QED
                BY <3>1 DEF Exists
        <2>3. QED
            BY <2>1, <2>2, Zenon
    <1>3. \A k \in Nat : Exists(k) => Exists(k + 1)
        BY <1>2
    <1>4. \A k \in Nat : Exists(k)
        BY <1>1, <1>3, NatInduction DEF Exists
    <1>5. Exists(len)
        BY <1>4, Zenon DEF Exists
    <1>6. QED
        BY <1>5 DEF Exists

LEMMA Agree ==
    ASSUME NEW Up(_, _), NEW b, NEW ms, NEW k \in Nat, NEW u, NEW w,
           u = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE Up(u[n - 1], ms[n]) ],
           w = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE Up(w[n - 1], ms[n]) ]
    PROVE  \A n \in Nat : n \in 0 .. k => u[n] = w[n]
PROOF
    <1> DEFINE Same(n) == n \in 0 .. k => u[n] = w[n]
    <1>1. Same(0)
        <2>1. u[0] = b
            BY Z3
        <2>2. w[0] = b
            BY Z3
        <2>3. QED
            BY <2>1, <2>2 DEF Same
    <1>2. ASSUME NEW n \in Nat, Same(n)
          PROVE  Same(n + 1)
        <2>1. CASE n + 1 \in 0 .. k
            <3>1. n + 1 \in 1 .. k
                BY <2>1, Z3
            <3>2. n \in 0 .. k
                BY <3>1, Z3
            <3>3. u[n] = w[n]
                BY <1>2, <3>2 DEF Same
            <3>4. u[n + 1] = Up(u[n], ms[n + 1])
                BY <3>1, Z3
            <3>5. w[n + 1] = Up(w[n], ms[n + 1])
                BY <3>1, Z3
            <3>6. u[n + 1] = w[n + 1]
                BY <3>3, <3>4, <3>5, Zenon
            <3>7. QED
                BY <2>1, <3>6 DEF Same
        <2>2. CASE n + 1 \notin 0 .. k
            BY <2>2 DEF Same
        <2>3. QED
            BY <2>1, <2>2
    <1>3. \A n \in Nat : Same(n) => Same(n + 1)
        BY <1>2
    <1>4. QED
        BY <1>1, <1>3, NatInduction DEF Same

LEMMA ChooseFold ==
    ASSUME NEW Up(_, _), NEW b, NEW ms, NEW k \in Nat
    PROVE  (CHOOSE z : z = [n \in 0 .. k |->
                              IF n = 0 THEN b
                              ELSE Up(z[n - 1], ms[n]) ])
            = [n \in 0 .. k |->
                 IF n = 0 THEN b
                 ELSE Up((CHOOSE z : z = [n \in 0 .. k |->
                                          IF n = 0 THEN b
                                          ELSE Up(z[n - 1], ms[n]) ])[n - 1],
                         ms[n]) ]
PROOF
    <1> DEFINE R(z) ==
            z = [n \in 0 .. k |->
                   IF n = 0 THEN b
                   ELSE Up(z[n - 1], ms[n]) ]
    <1>1. \E z : z = [n \in 0 .. k |->
                       IF n = 0 THEN b
                       ELSE Up(z[n - 1], ms[n]) ]
        BY ExistsAll
    <1>1b. \E z : R(z)
        BY <1>1 DEF R
    <1>2. PICK c : R(c)
        BY <1>1b
    <1>3. R(CHOOSE x : R(x))
        BY <1>2, Ax DEF R
    <1>4. QED
        BY <1>3 DEF R

LEMMA SameSrc ==
    ASSUME NEW Up(_, _), NEW b, NEW ms, NEW ns, NEW k \in Nat, NEW u,
           \A n \in 1 .. k : ms[n] = ns[n],
           u = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE Up(u[n - 1], ms[n]) ]
    PROVE  u = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE Up(u[n - 1], ns[n]) ]
PROOF
    <1> DEFINE h(n) ==
            IF n = 0 THEN b
            ELSE Up(u[n - 1], ms[n])
    <1> DEFINE e(n) ==
            IF n = 0 THEN b
            ELSE Up(u[n - 1], ns[n])
    <1> DEFINE g(m) ==
            IF m = 0 THEN b
            ELSE Up(u[m - 1], ms[m])
    <1>1. ASSUME NEW n \in 0 .. k
          PROVE  h(n) = e(n)
        <2>1. n = 0 => h(n) = e(n)
            BY Z3 DEF h, e
        <2>2. n \in 1 .. k => h(n) = e(n)
            BY Zenon DEF h, e
        <2>3. n = 0 \/ n \in 1 .. k
            BY Z3
        <2>4. QED
            BY <2>1, <2>2, <2>3, Z3
    <1>2. \A n \in 0 .. k : h(n) = e(n)
        BY <1>1
    <1>3. [n \in 0 .. k |-> h(n)] = [n \in 0 .. k |-> e(n)]
        BY <1>2, CtorEq DEF h, e
    <1>4. ASSUME NEW m \in 0 .. k
          PROVE  h(m) = g(m)
        BY Z3 DEF h, g
    <1>5. \A m \in 0 .. k : h(m) = g(m)
        BY <1>4
    <1>6. [n \in 0 .. k |-> h(n)] = [n \in 0 .. k |-> g(n)]
        BY <1>5, CtorEq DEF h, g
    <1>7. u = [n \in 0 .. k |-> g(n)]
        BY Zenon DEF g
    <1>8. u = [n \in 0 .. k |-> h(n)]
        BY <1>6, <1>7, Zenon
    <1>9. [n \in 0 .. k |-> e(n)] =
            [n \in 0 .. k |->
               IF n = 0 THEN b
               ELSE Up(u[n - 1], ns[n]) ]
        BY Z3 DEF e
    <1>10. QED
        BY <1>3, <1>8, <1>9, Zenon

LEMMA AgreeSucc ==
    ASSUME NEW Up(_, _), NEW b, NEW ms, NEW k \in Nat, NEW p, NEW q,
           p = [n \in 0 .. (k + 1) |->
                  IF n = 0 THEN b
                  ELSE Up(p[n - 1], ms[n]) ],
           q = [n \in 0 .. (k + 1) |->
                  IF n = 0 THEN b
                  ELSE Up(q[n - 1], ms[n]) ]
    PROVE  \A n \in Nat : n \in 0 .. (k + 1) => p[n] = q[n]
PROOF
    <1> DEFINE Same(n) == n \in 0 .. (k + 1) => p[n] = q[n]
    <1>1. Same(0)
        <2>1. p[0] = b
            BY Z3
        <2>2. q[0] = b
            BY Z3
        <2>3. QED
            BY <2>1, <2>2 DEF Same
    <1>2. ASSUME NEW n \in Nat, Same(n)
          PROVE  Same(n + 1)
        <2>1. CASE n + 1 \in 0 .. (k + 1)
            <3>1. n + 1 \in 1 .. (k + 1)
                BY <2>1, Z3
            <3>2. n \in 0 .. (k + 1)
                BY <3>1, Z3
            <3>3. p[n] = q[n]
                BY <1>2, <3>2 DEF Same
            <3>4. p[n + 1] = Up(p[n], ms[n + 1])
                BY <3>1, Z3
            <3>5. q[n + 1] = Up(q[n], ms[n + 1])
                BY <3>1, Z3
            <3>6. p[n + 1] = q[n + 1]
                BY <3>3, <3>4, <3>5, Zenon
            <3>7. QED
                BY <2>1, <3>6 DEF Same
        <2>2. CASE n + 1 \notin 0 .. (k + 1)
            BY <2>2 DEF Same
        <2>3. QED
            BY <2>1, <2>2
    <1>3. \A n \in Nat : Same(n) => Same(n + 1)
        BY <1>2
    <1>4. QED
        BY <1>1, <1>3, NatInduction DEF Same

LEMMA StepValue ==
    ASSUME NEW Up(_, _), NEW b, NEW ms, NEW k \in Nat, NEW u,
           u = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE Up(u[n - 1], ms[n]) ]
    PROVE  (CHOOSE z : z = [n \in 0 .. (k + 1) |->
                              IF n = 0 THEN b
                              ELSE Up(z[n - 1], ms[n]) ])[k + 1]
            = Up(u[k], ms[k + 1])
PROOF
    <1> DEFINE v == [n \in 0 .. (k + 1) |->
                       IF n <= k THEN u[n]
                       ELSE Up(u[k], ms[k + 1]) ]
    <1> DEFINE w == CHOOSE z : z = [n \in 0 .. (k + 1) |->
                                      IF n = 0 THEN b
                                      ELSE Up(z[n - 1], ms[n]) ]
    <1>1. k + 1 \in Nat
        BY Z3
    <1>2. v = [n \in 0 .. (k + 1) |->
                 IF n = 0 THEN b
                 ELSE Up(v[n - 1], ms[n]) ]
        BY Extend DEF v
    <1>3. w = [n \in 0 .. (k + 1) |->
                 IF n = 0 THEN b
                 ELSE Up(w[n - 1], ms[n]) ]
        BY <1>1, ChooseFold DEF w
    <1>4. \A n \in Nat : n \in 0 .. (k + 1) => v[n] = w[n]
        <2> HIDE DEF v, w
        <2>1. QED
            BY <1>2, <1>3, AgreeSucc
    <1>5. ASSUME NEW m \in 0 .. (k + 1)
          PROVE  m = k + 1 =>
                     v[m] = Up(u[k], ms[k + 1])
        BY Z3 DEF v
    <1>6. \A m \in 0 .. (k + 1) :
             m = k + 1 =>
                v[m] = Up(u[k], ms[k + 1])
        BY <1>5
    <1>7. k + 1 \in 0 .. (k + 1)
        BY <1>1, Z3
    <1>8. v[k + 1] = Up(u[k], ms[k + 1])
        BY <1>6, <1>7, Zenon
    <1>9. v[k + 1] = w[k + 1]
        BY <1>1, <1>4, <1>7, Zenon
    <1>10. QED
        BY <1>8, <1>9, Zenon DEF w

LEMMA AppendStep ==
    ASSUME NEW Up(_, _), NEW b, NEW S, NEW seq \in Seq(S), NEW msg \in S
    PROVE  LET u == CHOOSE z : z = [n \in 0 .. Len(seq) |->
                                      IF n = 0 THEN b
                                      ELSE Up(z[n - 1], seq[n]) ]
                src == Append(seq, msg)
                w == CHOOSE z : z = [n \in 0 .. (Len(seq) + 1) |->
                                      IF n = 0 THEN b
                                      ELSE Up(z[n - 1], src[n]) ]
            IN  w[Len(seq) + 1] = Up(u[Len(seq)], msg)
PROOF
    <1>1. Len(seq) \in Nat
        BY LenProperties
    <1>2. Len(seq) + 1 \in Nat
        BY <1>1, Z3
    <1> DEFINE src == Append(seq, msg)
    <1> DEFINE u == CHOOSE z : z = [n \in 0 .. Len(seq) |->
                                      IF n = 0 THEN b
                                      ELSE Up(z[n - 1], seq[n]) ]
    <1> DEFINE w == CHOOSE z : z = [n \in 0 .. (Len(seq) + 1) |->
                                      IF n = 0 THEN b
                                      ELSE Up(z[n - 1], src[n]) ]
    <1>3. u = [n \in 0 .. Len(seq) |->
                 IF n = 0 THEN b
                 ELSE Up(u[n - 1], seq[n]) ]
        BY <1>1, ChooseFold DEF u
    <1>4. \A i \in 1 .. Len(seq) : seq[i] = src[i]
        BY AppendProperties DEF src
    <1>5. src[Len(seq) + 1] = msg
        BY AppendProperties DEF src
    <1>6. u = [n \in 0 .. Len(seq) |->
                 IF n = 0 THEN b
                 ELSE Up(u[n - 1], src[n]) ]
        BY <1>1, <1>3, <1>4, SameSrc
    <1>7. (CHOOSE z : z = [n \in 0 .. (Len(seq) + 1) |->
                             IF n = 0 THEN b
                             ELSE Up(z[n - 1], src[n]) ])
            [Len(seq) + 1]
            = Up(u[Len(seq)], src[Len(seq) + 1])
        BY <1>1, <1>6, StepValue
    <1>8. w[Len(seq) + 1] = Up(u[Len(seq)], msg)
        BY <1>5, <1>7, Zenon DEF w
    <1>9. QED
        BY <1>8 DEF u, src, w

PickFresh(S, pre) ==
    CHOOSE y \in S : \A i \in 1 .. Len(pre) : pre[i] /= y

Step(S, pre) ==
    pre \o << PickFresh(S, pre) >>

EnumFn(S) ==
    LET f[k \in 0 .. Cardinality(S)] ==
          IF k = 0 THEN << >>
          ELSE Step(S, f[k - 1])
    IN  f

LEMMA FoldAtLen ==
    ASSUME NEW Up(_, _), NEW b, NEW ms, NEW len \in Nat
    PROVE  (CHOOSE z : z = [n \in 0 .. len |->
                              IF n = 0 THEN b
                              ELSE Up(z[n - 1], ms[n])])
            = [n \in 0 .. len |->
                 IF n = 0 THEN b
                 ELSE Up((CHOOSE z : z = [n \in 0 .. len |->
                                          IF n = 0 THEN b
                                          ELSE Up(z[n - 1], ms[n])])[n - 1],
                         ms[n])]
PROOF
    BY ChooseFold

LEMMA CardNat ==
    ASSUME NEW S, IsFiniteSet(S)
    PROVE  \E len \in Nat : len = Cardinality(S)
PROOF
    BY FS_CardinalityType, Zenon

LEMMA EnumAt ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW len \in Nat, len = Cardinality(S),
           NEW u,
           u = [k \in 0 .. len |->
                  IF k = 0 THEN << >>
                  ELSE u[k - 1] \o << CHOOSE y \in S :
                         \A i \in 1 .. Len(u[k - 1]) : u[k - 1][i] /= y >>]
    PROVE  /\ u[len] \in Seq(S)
           /\ IsInjective(u[len])
           /\ Len(u[len]) = len
           /\ Range(u[len]) = S
PROOF
    BY EnumSeq

LEMMA CloseFold ==
    ASSUME NEW Up(_, _), NEW b, NEW ms, NEW len \in Nat, NEW u,
           u = (CHOOSE z : z = [n \in 0 .. len |->
                                  IF n = 0 THEN b
                                  ELSE Up(z[n - 1], ms[n])]),
           (CHOOSE z : z = [n \in 0 .. len |->
                              IF n = 0 THEN b
                              ELSE Up(z[n - 1], ms[n])])
             = [n \in 0 .. len |->
                  IF n = 0 THEN b
                  ELSE Up((CHOOSE z : z = [n \in 0 .. len |->
                                           IF n = 0 THEN b
                                           ELSE Up(z[n - 1], ms[n])])[n - 1],
                          ms[n])]
    PROVE  u = [n \in 0 .. len |->
                  IF n = 0 THEN b
                  ELSE Up(u[n - 1], ms[n])]
PROOF
    BY Zenon

LEMMA AtUp ==
    ASSUME NEW Up(_, _), NEW b, NEW ms, NEW len \in Nat, NEW u,
           u = (CHOOSE z : z = [n \in 0 .. len |->
                                  IF n = 0 THEN b
                                  ELSE Up(z[n - 1], ms[n])])
    PROVE  u = [n \in 0 .. len |->
                  IF n = 0 THEN b
                  ELSE Up(u[n - 1], ms[n])]
PROOF
    <1>1. (CHOOSE z : z = [n \in 0 .. len |->
                             IF n = 0 THEN b
                             ELSE Up(z[n - 1], ms[n])])
            = [n \in 0 .. len |->
                 IF n = 0 THEN b
                 ELSE Up((CHOOSE z : z = [n \in 0 .. len |->
                                          IF n = 0 THEN b
                                          ELSE Up(z[n - 1], ms[n])])[n - 1],
                         ms[n])]
        BY FoldAtLen
    <1>2. QED
        BY <1>1, CloseFold

LEMMA SetEnum ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW len \in Nat, len = Cardinality(S)
    PROVE  /\ EnumFn(S)[len] \in Seq(S)
           /\ IsInjective(EnumFn(S)[len])
           /\ Len(EnumFn(S)[len]) = len
           /\ Range(EnumFn(S)[len]) = S
PROOF
    <1> DEFINE Up(pre, x) == Step(S, pre)
    <1> DEFINE ms == [j \in Nat |-> 0]
    <1>1. PICK u :
            u = (CHOOSE z : z = [n \in 0 .. len |->
                                   IF n = 0 THEN << >>
                                   ELSE Up(z[n - 1], ms[n])])
        BY Zenon
    <1>2. u = [n \in 0 .. len |->
                 IF n = 0 THEN << >>
                 ELSE Up(u[n - 1], ms[n])]
        <2> HIDE DEF Up, ms
        <2>1. QED
            BY <1>1, AtUp
    <1>3. u = [n \in 0 .. len |->
                 IF n = 0 THEN << >>
                 ELSE u[n - 1] \o << CHOOSE y \in S :
                        \A i \in 1 .. Len(u[n - 1]) : u[n - 1][i] /= y >>]
        BY <1>2 DEF Up, Step, PickFresh
    <1>4. u = [k \in 0 .. len |->
                 IF k = 0 THEN << >>
                 ELSE u[k - 1] \o << CHOOSE y \in S :
                        \A i \in 1 .. Len(u[k - 1]) : u[k - 1][i] /= y >>]
        BY <1>3, Zenon
    <1>5. /\ u[len] \in Seq(S)
          /\ IsInjective(u[len])
          /\ Len(u[len]) = len
          /\ Range(u[len]) = S
        BY <1>4, EnumAt
    <1>6. EnumFn(S) = u
        BY <1>1 DEF EnumFn, Up, Step, PickFresh, ms
    <1>7. QED
        BY <1>5, <1>6

(* The list Requests builds: the element at the end of the same fold. *)
SeqOf(S) ==
    LET f[k \in 0 .. Cardinality(S)] ==
          IF k = 0 THEN
              << >>
          ELSE
              LET pre == f[k - 1]
              IN  pre \o << CHOOSE y \in S : \A n \in 1 .. Len(pre) : pre[n] /= y >>
    IN  f[Cardinality(S)]

LEMMA SeqOfFn ==
    ASSUME NEW S, NEW len, len = Cardinality(S)
    PROVE  SeqOf(S) = EnumFn(S)[len]
PROOF
    BY DEF SeqOf, EnumFn, Step, PickFresh

LEMMA SeqOfEnum ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW len \in Nat, len = Cardinality(S)
    PROVE  /\ SeqOf(S) \in Seq(S)
           /\ IsInjective(SeqOf(S))
           /\ Len(SeqOf(S)) = len
           /\ Range(SeqOf(S)) = S
PROOF
    BY SetEnum, SeqOfFn

LEMMA SeqOfAny ==
    ASSUME NEW S, IsFiniteSet(S)
    PROVE  /\ SeqOf(S) \in Seq(S)
           /\ IsInjective(SeqOf(S))
           /\ Len(SeqOf(S)) = Cardinality(S)
           /\ Range(SeqOf(S)) = S
PROOF
    <1>1. PICK len \in Nat : len = Cardinality(S)
        BY CardNat
    <1>2. QED
        BY <1>1, SeqOfEnum

=============================================================================
