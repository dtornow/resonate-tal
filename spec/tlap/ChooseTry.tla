---------------------------- MODULE ChooseTry ----------------------------
EXTENDS Integers, Sequences, NaturalsInduction, SequenceTheorems, TLAPS

LEMMA CtorEq ==
    ASSUME NEW S, NEW h(_), NEW e(_),
           \A x \in S : h(x) = e(x)
    PROVE  [x \in S |-> h(x)] = [x \in S |-> e(x)]
PROOF
    BY Zenon

LEMMA Extend ==
    ASSUME NEW b, NEW ms, NEW k \in Nat, NEW u,
           u = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE { x \in u[n - 1] : TRUE } \cup {ms[n]} ]
    PROVE  LET v == [n \in 0 .. (k + 1) |->
                       IF n <= k THEN u[n]
                       ELSE { x \in u[k] : TRUE } \cup {ms[k + 1]} ]
           IN  v = [n \in 0 .. (k + 1) |->
                      IF n = 0 THEN b
                      ELSE { x \in v[n - 1] : TRUE } \cup {ms[n]} ]
PROOF
    <1> DEFINE v == [n \in 0 .. (k + 1) |->
                       IF n <= k THEN u[n]
                       ELSE { x \in u[k] : TRUE } \cup {ms[k + 1]} ]
    <1> DEFINE w == [n \in 0 .. (k + 1) |->
                       IF n = 0 THEN b
                       ELSE { x \in v[n - 1] : TRUE } \cup {ms[n]} ]
    <1> DEFINE hv(n) ==
            IF n <= k THEN u[n]
            ELSE { x \in u[k] : TRUE } \cup {ms[k + 1]}
    <1> DEFINE hw(n) ==
            IF n = 0 THEN b
            ELSE { x \in v[n - 1] : TRUE } \cup {ms[n]}
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
        <2>4. n \in 1 .. k => u[n] = { x \in u[n - 1] : TRUE } \cup {ms[n]}
            BY Z3
        <2>5. n \in 1 .. k => w[n] = { x \in v[n - 1] : TRUE } \cup {ms[n]}
            BY Z3 DEF w
        <2>6. n \in 1 .. k => v[n] = w[n]
            BY <2>2, <2>3b, <2>4, <2>5, Zenon
        <2>7. n = k + 1 => v[n] = { x \in u[k] : TRUE } \cup {ms[k + 1]}
            BY Z3 DEF v
        <2>8a. k \in 0 .. k /\ k \in 0 .. (k + 1)
            BY Z3
        <2>8. v[k] = u[k]
            BY <2>0b, <2>8a, Zenon
        <2>9. n = k + 1 => n - 1 = k
            BY Z3
        <2>10. n = k + 1 => w[n] = { x \in v[k] : TRUE } \cup {ms[k + 1]}
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
    ASSUME NEW b, NEW ms
    PROVE  \A k \in Nat :
              \E u : u = [n \in 0 .. k |->
                            IF n = 0 THEN b
                            ELSE { x \in u[n - 1] : TRUE } \cup {ms[n]} ]
PROOF
    <1> DEFINE Exists(k) ==
            \E u : u = [n \in 0 .. k |->
                          IF n = 0 THEN b
                          ELSE { x \in u[n - 1] : TRUE } \cup {ms[n]} ]
    <1>1. Exists(0)
        <2> DEFINE f == [n \in 0 .. 0 |-> b]
        <2>1. f = [n \in 0 .. 0 |-> IF n = 0 THEN b
                                    ELSE { x \in f[n - 1] : TRUE } \cup {ms[n]} ]
            BY Z3 DEF f
        <2>2. QED
            BY <2>1 DEF Exists
    <1>2. ASSUME NEW k \in Nat, Exists(k)
          PROVE  Exists(k + 1)
        <2> DEFINE Q(u) ==
                u = [n \in 0 .. k |->
                       IF n = 0 THEN b
                       ELSE { x \in u[n - 1] : TRUE } \cup {ms[n]} ]
        <2>1. \E u : Q(u)
            BY <1>2 DEF Exists, Q
        <2>2. ASSUME NEW u, Q(u)
              PROVE  Exists(k + 1)
            <3> DEFINE v == [n \in 0 .. (k + 1) |->
                               IF n <= k THEN u[n]
                               ELSE { x \in u[k] : TRUE } \cup {ms[k + 1]} ]
            <3>1. v = [n \in 0 .. (k + 1) |->
                         IF n = 0 THEN b
                         ELSE { x \in v[n - 1] : TRUE } \cup {ms[n]} ]
                BY <1>2, <2>2, Extend DEF v, Q
            <3>2. QED
                BY <3>1 DEF Exists
        <2>3. QED
            BY <2>1, <2>2, Zenon
    <1>3. \A k \in Nat : Exists(k) => Exists(k + 1)
        BY <1>2
    <1>4. QED
        BY <1>1, <1>3, NatInduction DEF Exists

LEMMA Agree ==
    ASSUME NEW b, NEW ms, NEW k \in Nat, NEW u, NEW w,
           u = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE { x \in u[n - 1] : TRUE } \cup {ms[n]} ],
           w = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE { x \in w[n - 1] : TRUE } \cup {ms[n]} ]
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
            <3>4. u[n + 1] = { x \in u[n] : TRUE } \cup {ms[n + 1]}
                BY <3>1, Z3
            <3>5. w[n + 1] = { x \in w[n] : TRUE } \cup {ms[n + 1]}
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

LEMMA Ax ==
    ASSUME NEW Q(_), NEW c, Q(c)
    PROVE  Q(CHOOSE x : Q(x))
PROOF
    BY Zenon

LEMMA ChooseFold ==
    ASSUME NEW b, NEW ms, NEW k \in Nat
    PROVE  (CHOOSE z : z = [n \in 0 .. k |->
                              IF n = 0 THEN b
                              ELSE { x \in z[n - 1] : TRUE } \cup {ms[n]} ])
            = [n \in 0 .. k |->
                 IF n = 0 THEN b
                 ELSE { x \in (CHOOSE z : z = [n \in 0 .. k |->
                                          IF n = 0 THEN b
                                          ELSE { x \in z[n - 1] : TRUE }
                                                  \cup {ms[n]} ])[n - 1]
                            : TRUE } \cup {ms[n]} ]
PROOF
    <1> DEFINE R(z) ==
            z = [n \in 0 .. k |->
                   IF n = 0 THEN b
                   ELSE { x \in z[n - 1] : TRUE } \cup {ms[n]} ]
    <1>1. \E z : R(z)
        BY ExistsAll DEF R
    <1>2. PICK c : R(c)
        BY <1>1
    <1>3. R(CHOOSE x : R(x))
        BY <1>2, Ax DEF R
    <1>4. QED
        BY <1>3 DEF R

LEMMA SameSrc ==
    ASSUME NEW b, NEW ms, NEW ns, NEW k \in Nat, NEW u,
           \A n \in 1 .. k : ms[n] = ns[n],
           u = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE { x \in u[n - 1] : TRUE } \cup {ms[n]} ]
    PROVE  u = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE { x \in u[n - 1] : TRUE } \cup {ns[n]} ]
PROOF
    <1> DEFINE h(n) ==
            IF n = 0 THEN b
            ELSE { x \in u[n - 1] : TRUE } \cup {ms[n]}
    <1> DEFINE e(n) ==
            IF n = 0 THEN b
            ELSE { x \in u[n - 1] : TRUE } \cup {ns[n]}
    <1> DEFINE g(m) ==
            IF m = 0 THEN b
            ELSE { x \in u[m - 1] : TRUE } \cup {ms[m]}
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
               ELSE { x \in u[n - 1] : TRUE } \cup {ns[n]} ]
        BY Z3 DEF e
    <1>10. QED
        BY <1>3, <1>8, <1>9, Zenon

LEMMA AgreeSucc ==
    ASSUME NEW b, NEW ms, NEW k \in Nat, NEW p, NEW q,
           p = [n \in 0 .. (k + 1) |->
                  IF n = 0 THEN b
                  ELSE { x \in p[n - 1] : TRUE } \cup {ms[n]} ],
           q = [n \in 0 .. (k + 1) |->
                  IF n = 0 THEN b
                  ELSE { x \in q[n - 1] : TRUE } \cup {ms[n]} ]
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
            <3>4. p[n + 1] = { x \in p[n] : TRUE } \cup {ms[n + 1]}
                BY <3>1, Z3
            <3>5. q[n + 1] = { x \in q[n] : TRUE } \cup {ms[n + 1]}
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
    ASSUME NEW b, NEW ms, NEW k \in Nat, NEW u,
           u = [n \in 0 .. k |->
                  IF n = 0 THEN b
                  ELSE { x \in u[n - 1] : TRUE } \cup {ms[n]} ]
    PROVE  (CHOOSE z : z = [n \in 0 .. (k + 1) |->
                              IF n = 0 THEN b
                              ELSE { x \in z[n - 1] : TRUE } \cup {ms[n]} ])[k + 1]
            = { x \in u[k] : TRUE } \cup {ms[k + 1]}
PROOF
    <1> DEFINE v == [n \in 0 .. (k + 1) |->
                       IF n <= k THEN u[n]
                       ELSE { x \in u[k] : TRUE } \cup {ms[k + 1]} ]
    <1> DEFINE w == CHOOSE z : z = [n \in 0 .. (k + 1) |->
                                      IF n = 0 THEN b
                                      ELSE { x \in z[n - 1] : TRUE } \cup {ms[n]} ]
    <1>1. k + 1 \in Nat
        BY Z3
    <1>2. v = [n \in 0 .. (k + 1) |->
                 IF n = 0 THEN b
                 ELSE { x \in v[n - 1] : TRUE } \cup {ms[n]} ]
        BY Extend DEF v
    <1>3. w = [n \in 0 .. (k + 1) |->
                 IF n = 0 THEN b
                 ELSE { x \in w[n - 1] : TRUE } \cup {ms[n]} ]
        BY <1>1, ChooseFold DEF w
    <1>4. \A n \in Nat : n \in 0 .. (k + 1) => v[n] = w[n]
        <2> HIDE DEF v, w
        <2>1. QED
            BY <1>2, <1>3, AgreeSucc
    <1>5. ASSUME NEW m \in 0 .. (k + 1)
          PROVE  m = k + 1 =>
                     v[m] = { x \in u[k] : TRUE } \cup {ms[k + 1]}
        BY Z3 DEF v
    <1>6. \A m \in 0 .. (k + 1) :
             m = k + 1 =>
                v[m] = { x \in u[k] : TRUE } \cup {ms[k + 1]}
        BY <1>5
    <1>7. k + 1 \in 0 .. (k + 1)
        BY <1>1, Z3
    <1>8. v[k + 1] = { x \in u[k] : TRUE } \cup {ms[k + 1]}
        BY <1>6, <1>7, Zenon
    <1>9. v[k + 1] = w[k + 1]
        BY <1>1, <1>4, <1>7, Zenon
    <1>10. QED
        BY <1>8, <1>9, Zenon DEF w

LEMMA AppendStep ==
    ASSUME NEW b, NEW S, NEW seq \in Seq(S), NEW msg \in S
    PROVE  LET u == CHOOSE z : z = [n \in 0 .. Len(seq) |->
                                      IF n = 0 THEN b
                                      ELSE { x \in z[n - 1] : TRUE }
                                              \cup {seq[n]} ]
                src == Append(seq, msg)
                w == CHOOSE z : z = [n \in 0 .. (Len(seq) + 1) |->
                                      IF n = 0 THEN b
                                      ELSE { x \in z[n - 1] : TRUE }
                                              \cup {src[n]} ]
            IN  w[Len(seq) + 1] = { x \in u[Len(seq)] : TRUE } \cup {msg}
PROOF
    <1>1. Len(seq) \in Nat
        BY LenProperties
    <1>2. Len(seq) + 1 \in Nat
        BY <1>1, Z3
    <1> DEFINE src == Append(seq, msg)
    <1> DEFINE u == CHOOSE z : z = [n \in 0 .. Len(seq) |->
                                      IF n = 0 THEN b
                                      ELSE { x \in z[n - 1] : TRUE }
                                              \cup {seq[n]} ]
    <1> DEFINE w == CHOOSE z : z = [n \in 0 .. (Len(seq) + 1) |->
                                      IF n = 0 THEN b
                                      ELSE { x \in z[n - 1] : TRUE }
                                              \cup {src[n]} ]
    <1>3. u = [n \in 0 .. Len(seq) |->
                 IF n = 0 THEN b
                 ELSE { x \in u[n - 1] : TRUE } \cup {seq[n]} ]
        BY <1>1, ChooseFold DEF u
    <1>4. \A i \in 1 .. Len(seq) : seq[i] = src[i]
        BY AppendProperties DEF src
    <1>5. src[Len(seq) + 1] = msg
        BY AppendProperties DEF src
    <1>6. u = [n \in 0 .. Len(seq) |->
                 IF n = 0 THEN b
                 ELSE { x \in u[n - 1] : TRUE } \cup {src[n]} ]
        BY <1>1, <1>3, <1>4, SameSrc
    <1>7. (CHOOSE z : z = [n \in 0 .. (Len(seq) + 1) |->
                             IF n = 0 THEN b
                             ELSE { x \in z[n - 1] : TRUE } \cup {src[n]} ])
            [Len(seq) + 1]
            = { x \in u[Len(seq)] : TRUE } \cup {src[Len(seq) + 1]}
        BY <1>1, <1>6, StepValue
    <1>8. w[Len(seq) + 1] = { x \in u[Len(seq)] : TRUE } \cup {msg}
        BY <1>5, <1>7, Zenon DEF w
    <1>9. QED
        BY <1>8 DEF u, src, w

=============================================================================
