------------------------------ MODULE ToSeq ------------------------------
EXTENDS Requests, FoldTry

LEMMA SetToSeqIs ==
    ASSUME NEW S
    PROVE  SetToSeq(S) = SeqOf(S)
PROOF
    BY DEF SetToSeq, SeqOf

LEMMA SetToSeqEnum ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW len \in Nat, len = Cardinality(S)
    PROVE  /\ SetToSeq(S) \in Seq(S)
           /\ IsInjective(SetToSeq(S))
           /\ Len(SetToSeq(S)) = len
           /\ Range(SetToSeq(S)) = S
PROOF
    BY SetToSeqIs, SeqOfEnum

LEMMA SetToSeqAny ==
    ASSUME NEW S, IsFiniteSet(S)
    PROVE  /\ SetToSeq(S) \in Seq(S)
           /\ IsInjective(SetToSeq(S))
           /\ Len(SetToSeq(S)) = Cardinality(S)
           /\ Range(SetToSeq(S)) = S
PROOF
    BY SetToSeqIs, SeqOfAny

=============================================================================
