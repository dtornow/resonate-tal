------------------------ MODULE AbstractBatchProbe ------------------------
(* Small executable fixture for the callback -> retry stage handoff. *)
EXTENDS AbstractBatch

AwaitedId ==
    CHOOSE id \in Id : TRUE

AwaiterId ==
    CHOOSE id \in Id : id /= AwaitedId

ExternalTags ==
    CHOOSE tags \in Tags : tags.external

TargetedTags ==
    CHOOSE tags \in Tags : tags.targeted

SomeValue ==
    CHOOSE value \in Value : TRUE

AwaitedObject ==
    LET req == [id        |-> AwaitedId,
                timeoutAt |-> 1,
                param     |-> SomeValue,
                tags      |-> ExternalTags]
    IN  [Project(New(req, 0), 1) EXCEPT
             !.promise.callbacks = {AwaiterId}]

AwaiterObject ==
    LET req  == [id        |-> AwaiterId,
                 timeoutAt |-> 2,
                 param     |-> SomeValue,
                 tags      |-> TargetedTags]
        born == New(req, 0)
    IN  [born EXCEPT
             !.task.state          = "suspended",
             !.task.retryTimeoutAt = NoTime]

ProbeInit ==
    /\ objects = Write(Write(EmptyFn, AwaitedId, AwaitedObject),
                       AwaiterId, AwaiterObject)
    /\ network = {}
    /\ now = 1

ProbeNext ==
    Batch

=============================================================================
