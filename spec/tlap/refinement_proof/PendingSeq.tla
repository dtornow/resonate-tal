----------------------------- MODULE PendingSeq -----------------------------
(* A perform queue is put-timeouts, one document write, then del-timeouts.
   The document write is the only entry whose tag is PutDocument, and it
   stays that entry after the prefix is consumed. *)
EXTENDS Naturals, Sequences, SequenceTheorems, TLAPS

Docs(seq, docb, sent) ==
    \A j \in DOMAIN seq :
        seq[j].tag = "PutDocument" =>
            seq[j].body = docb /\ seq[j].sends = sent

LEMMA LenNat ==
    ASSUME NEW s
    PROVE  Len(s) \in Nat
PROOF
    BY DEF Len

LEMMA RangeEq ==
    ASSUME NEW a \in Nat, NEW b \in Nat, 1 .. a = 1 .. b
    PROVE  a = b
PROOF
    BY SMT

LEMMA FunLen ==
    ASSUME NEW n \in Nat, NEW e(_), NEW S,
           \A i \in 1 .. n : e(i) \in S
    PROVE  /\ [i \in 1 .. n |-> e(i)] \in Seq(S)
           /\ Len([i \in 1 .. n |-> e(i)]) = n
           /\ DOMAIN [i \in 1 .. n |-> e(i)] = 1 .. n
           /\ \A i \in 1 .. n : [i \in 1 .. n |-> e(i)][i] = e(i)
PROOF
    <1> DEFINE f == [i \in 1 .. n |-> e(i)]
    <1>1. f \in Seq(S)
        BY IsASeq DEF f
    <1>2. DOMAIN f = 1 .. n
        OBVIOUS
    <1>3. Len(f) \in Nat /\ DOMAIN f = 1 .. Len(f)
        BY <1>1, LenProperties
    <1>4. Len(f) = n
        BY <1>2, <1>3, RangeEq
    <1>5. \A i \in 1 .. n : f[i] = e(i)
        OBVIOUS
    <1>6. QED
        BY <1>1, <1>2, <1>4, <1>5 DEF f

LEMMA OneSeq ==
    ASSUME NEW S, NEW rec \in S
    PROVE  /\ <<rec>> \in Seq(S)
           /\ Len(<<rec>>) = 1
           /\ <<rec>>[1] = rec
PROOF
    <1> DEFINE f == [i \in 1 .. 1 |-> rec]
    <1>1. \A i \in 1 .. 1 : rec \in S
        OBVIOUS
    <1>2. f \in Seq(S)
        BY <1>1, IsASeq DEF f
    <1>3. DOMAIN f = 1 .. 1
        OBVIOUS
    <1>4. Len(f) \in Nat /\ DOMAIN f = 1 .. Len(f)
        BY <1>2, LenProperties
    <1>5. Len(f) = 1
        BY <1>3, <1>4, RangeEq
    <1>6. f[1] = rec
        OBVIOUS
    <1>7. <<rec>> = f
        OBVIOUS
    <1>8. QED
        BY <1>2, <1>5, <1>6, <1>7 DEF f

LEMMA OnlyDoc ==
    ASSUME NEW n \in Nat, NEW m \in Nat,
           NEW puts, NEW dels, NEW docb, NEW sent,
           NEW pre, NEW post, NEW rec, NEW seq,
           pre = [i \in 1 .. n |-> [tag |-> "PutTimeout", entry |-> puts[i]]],
           post = [i \in 1 .. m |-> [tag |-> "DelTimeout", entry |-> dels[i]]],
           rec = [tag |-> "PutDocument", body |-> docb, sends |-> sent],
           seq = (pre \o <<rec>>) \o post
    PROVE  /\ seq \in Seq(Range(seq))
           /\ Docs(seq, docb, sent)
PROOF
    <1> DEFINE putAt(i) == [tag |-> "PutTimeout", entry |-> puts[i]]
               delAt(i) == [tag |-> "DelTimeout", entry |-> dels[i]]
               S == {putAt(i) : i \in 1 .. n} \cup {rec} \cup {delAt(i) : i \in 1 .. m}
               mid == pre \o <<rec>>
    <1>1. \A i \in 1 .. n : putAt(i) \in S
        BY Zenon DEF S
    <1>2. rec \in S
        BY Zenon DEF S
    <1>3. \A i \in 1 .. m : delAt(i) \in S
        BY Zenon DEF S
    <1>4. pre = [i \in 1 .. n |-> putAt(i)]
        BY DEF putAt
    <1>5. post = [i \in 1 .. m |-> delAt(i)]
        BY DEF delAt
    <1>6. [i \in 1 .. n |-> putAt(i)] \in Seq(S)
        BY <1>1, IsASeq
    <1>7. pre \in Seq(S)
        BY <1>4, <1>6
    <1>8. DOMAIN pre = 1 .. n /\ \A i \in 1 .. n : pre[i] = putAt(i)
        BY <1>4, Zenon
    <1>9. Len(pre) \in Nat /\ DOMAIN pre = 1 .. Len(pre)
        BY <1>7, LenProperties
    <1>10. Len(pre) = n
        BY <1>8, <1>9, RangeEq
    <1>11. [i \in 1 .. m |-> delAt(i)] \in Seq(S)
        BY <1>3, IsASeq
    <1>12. post \in Seq(S)
        BY <1>5, <1>11
    <1>13. DOMAIN post = 1 .. m /\ \A i \in 1 .. m : post[i] = delAt(i)
        BY <1>5, Zenon
    <1>14. Len(post) \in Nat /\ DOMAIN post = 1 .. Len(post)
        BY <1>12, LenProperties
    <1>15. Len(post) = m
        BY <1>13, <1>14, RangeEq
    <1>16. /\ <<rec>> \in Seq(S)
           /\ Len(<<rec>>) = 1
           /\ <<rec>>[1] = rec
        BY <1>2, OneSeq
    <1>17. /\ mid \in Seq(S)
           /\ Len(mid) = n + 1
           /\ \A i \in 1 .. n + 1 :
                mid[i] = IF i <= n THEN pre[i] ELSE <<rec>>[i - n]
        <2>1. /\ mid \in Seq(S)
              /\ Len(mid) = Len(pre) + Len(<<rec>>)
              /\ \A i \in 1 .. Len(pre) + Len(<<rec>>) :
                   mid[i] = IF i <= Len(pre) THEN pre[i]
                            ELSE <<rec>>[i - Len(pre)]
            BY <1>7, <1>16, ConcatProperties DEF mid
        <2>2. Len(pre) = n /\ Len(<<rec>>) = 1
            BY <1>10, <1>16
        <2>3. Len(mid) = n + 1
            BY <2>1, <2>2, SMT
        <2>4. ASSUME NEW i \in 1 .. n + 1
              PROVE  mid[i] = IF i <= n THEN pre[i] ELSE <<rec>>[i - n]
            <3>1. i \in 1 .. Len(pre) + Len(<<rec>>)
                BY <2>2, <2>4, SMT
            <3>2. mid[i] = IF i <= Len(pre) THEN pre[i]
                           ELSE <<rec>>[i - Len(pre)]
                BY <2>1, <3>1
            <3>3. QED
                BY <2>2, <3>2, SMT
        <2>5. QED
            BY <2>1, <2>3, <2>4
    <1>18. seq = mid \o post
        BY DEF mid
    <1>19. /\ seq \in Seq(S)
           /\ Len(seq) = (n + 1) + m
           /\ \A i \in 1 .. (n + 1) + m :
                seq[i] = IF i <= n + 1 THEN mid[i] ELSE post[i - (n + 1)]
        <2>1. /\ mid \o post \in Seq(S)
              /\ Len(mid \o post) = Len(mid) + Len(post)
              /\ \A i \in 1 .. Len(mid) + Len(post) :
                   (mid \o post)[i] = IF i <= Len(mid) THEN mid[i]
                                      ELSE post[i - Len(mid)]
            <3>1. mid \in Seq(S)
                BY <1>17, Zenon
            <3>2. QED
                BY <1>12, <3>1, ConcatProperties
        <2>2. /\ seq \in Seq(S)
              /\ Len(seq) = Len(mid) + Len(post)
              /\ \A i \in 1 .. Len(mid) + Len(post) :
                   seq[i] = IF i <= Len(mid) THEN mid[i]
                            ELSE post[i - Len(mid)]
            BY <1>18, <2>1, Isa
        <2>3. Len(mid) = n + 1 /\ Len(post) = m
            BY <1>15, <1>17
        <2>4. Len(seq) = (n + 1) + m
            BY <2>2, <2>3, SMT
        <2>5. ASSUME NEW i \in 1 .. (n + 1) + m
              PROVE  seq[i] = IF i <= n + 1 THEN mid[i] ELSE post[i - (n + 1)]
            <3>1. i \in 1 .. Len(mid) + Len(post)
                BY <2>3, <2>5, SMT
            <3>2. seq[i] = IF i <= Len(mid) THEN mid[i] ELSE post[i - Len(mid)]
                BY <2>2, <3>1
            <3>3. QED
                BY <2>3, <3>2, SMT
        <2>6. QED
            BY <2>2, <2>4, <2>5
    <1>20. seq \in Seq(Range(seq))
        BY <1>19, SeqOfRange
    <1>21. DOMAIN seq = 1 .. Len(seq)
        BY <1>19, LenProperties
    <1>22. \A i \in 1 .. n : putAt(i).tag = "PutTimeout"
        BY Zenon DEF putAt
    <1>23. \A i \in 1 .. m : delAt(i).tag = "DelTimeout"
        BY Zenon DEF delAt
    <1>24. rec.body = docb /\ rec.sends = sent
        BY Zenon
    <1>25. ASSUME NEW i \in 1 .. n
           PROVE  seq[i] = pre[i]
        <2>1. i \in 1 .. n + 1 /\ i <= n
            BY <1>25, SMT
        <2>2. mid[i] = pre[i]
            BY <1>17, <2>1
        <2>3. seq[i] = mid[i]
            BY <1>19, <2>1
        <2>4. QED
            BY <2>2, <2>3
    <1>26. n + 1 \in 1 .. Len(seq) /\ seq[n + 1] = rec
        <2>1. n + 1 \in 1 .. (n + 1) + m
            BY SMT
        <2>2. Len(seq) = (n + 1) + m
            BY <1>19
        <2>3. seq[n + 1] = mid[n + 1]
            BY <1>19, <2>1, <2>2, SMT
        <2>4. n + 1 > n /\ (n + 1) - n = 1
            BY SMT
        <2>5. mid[n + 1] = <<rec>>[1]
            BY <1>17, <2>1, <2>4
        <2>6. <<rec>>[1] = rec
            BY <1>16
        <2>7. QED
            BY <2>1, <2>2, <2>3, <2>5, <2>6
    <1>27. ASSUME NEW i \in 1 .. m
           PROVE  seq[(n + 1) + i] = post[i]
        <2>1. (n + 1) + i \in 1 .. (n + 1) + m
            BY <1>27, SMT
        <2>2. (n + 1) + i > n + 1
            BY <1>27, SMT
        <2>3. seq[(n + 1) + i] = post[((n + 1) + i) - (n + 1)]
            BY <1>19, <2>1, <2>2
        <2>4. ((n + 1) + i) - (n + 1) = i
            BY SMT
        <2>5. QED
            BY <2>3, <2>4
    <1>28. ASSUME NEW j \in DOMAIN seq, seq[j].tag = "PutDocument"
           PROVE  seq[j].body = docb /\ seq[j].sends = sent
        <2>1. j \in 1 .. (n + 1) + m
            BY <1>19, <1>21, <1>28
        <2>2. j \in 1 .. n \/ j = n + 1 \/ j \in (n + 2) .. ((n + 1) + m)
            BY <2>1, SMT
        <2>3. CASE j \in 1 .. n
            <3>1. seq[j] = pre[j]
                BY <1>25, <2>3
            <3>2. pre[j] = putAt(j)
                BY <1>8, <2>3
            <3>3. seq[j].tag = "PutTimeout"
                BY <1>22, <2>3, <3>1, <3>2, Zenon
            <3>4. FALSE
                BY <1>28, <3>3, Zenon
            <3>5. QED
                BY <3>4
        <2>4. CASE j = n + 1
            <3>1. seq[j] = rec
                BY <1>26, <2>4
            <3>2. QED
                BY <1>24, <3>1, Zenon
        <2>5. CASE j \in (n + 2) .. ((n + 1) + m)
            <3> DEFINE k == j - (n + 1)
            <3>1. k \in 1 .. m
                BY <2>5, SMT DEF k
            <3>2. seq[j] = post[k]
                BY <1>27, <2>5, <3>1 DEF k
            <3>3. post[k] = delAt(k)
                BY <1>13, <3>1
            <3>4. seq[j].tag = "DelTimeout"
                BY <1>23, <3>1, <3>2, <3>3, Zenon
            <3>5. FALSE
                BY <1>28, <3>4, Zenon
            <3>6. QED
                BY <3>5
        <2>6. QED
            BY <2>2, <2>3, <2>4, <2>5
    <1>29. Docs(seq, docb, sent)
        BY <1>28 DEF Docs
    <1>30. QED
        BY <1>20, <1>29

LEMMA TailDoc ==
    ASSUME NEW seq, NEW docb, NEW sent,
           seq \in Seq(Range(seq)),
           seq # << >>,
           Docs(seq, docb, sent)
    PROVE  /\ Tail(seq) \in Seq(Range(Tail(seq)))
           /\ Docs(Tail(seq), docb, sent)
PROOF
    <1>1. ASSUME NEW SS, SS = Range(seq)
          PROVE  /\ Tail(seq) \in Seq(SS)
                 /\ Len(Tail(seq)) = Len(seq) - 1
                 /\ \A i \in 1 .. Len(Tail(seq)) : Tail(seq)[i] = seq[i + 1]
        BY <1>1, HeadTailProperties
    <1>2. Tail(seq) \in Seq(Range(seq))
        BY <1>1
    <1>3. Tail(seq) \in Seq(Range(Tail(seq)))
        BY <1>2, SeqOfRange
    <1>4. Len(seq) \in Nat /\ DOMAIN seq = 1 .. Len(seq)
        BY LenProperties
    <1>5. Len(Tail(seq)) = Len(seq) - 1 /\ DOMAIN Tail(seq) = 1 .. Len(Tail(seq))
        BY <1>1, <1>2, LenProperties
    <1>6. ASSUME NEW j \in DOMAIN Tail(seq)
          PROVE  Tail(seq)[j].tag = "PutDocument" =>
                    Tail(seq)[j].body = docb /\ Tail(seq)[j].sends = sent
        <2>1. j \in 1 .. Len(Tail(seq))
            BY <1>5, <1>6
        <2>2. j + 1 \in DOMAIN seq
            BY <1>4, <1>5, <2>1, SMT
        <2>3. Tail(seq)[j] = seq[j + 1]
            BY <1>1, <2>1
        <2>4. QED
            BY <2>2, <2>3 DEF Docs
    <1>7. Docs(Tail(seq), docb, sent)
        BY <1>6 DEF Docs
    <1>8. QED
        BY <1>3, <1>7

=============================================================================
