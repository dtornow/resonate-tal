----------------------- MODULE SplitNetworkConcrete -----------------------
(***************************************************************************)
(* Additive prototype of Concrete with one semantic change: the document   *)
(* CAS publishes messages to ghost `offers`, not to `network`. SendOffer    *)
(* and DropOffer are independent best-effort actions. The existing          *)
(* Concrete module is instantiated and remains untouched.                  *)
(***************************************************************************)
EXTENDS Requests

VARIABLES
    docs,
    timeouts,
    offers,
    network,
    steps,
    now

vars ==
    <<docs, timeouts, offers, network, steps, now>>

(* Concrete's operators are reused with its old outbox parameter hidden
   behind `network`. None of the reused process actions writes it; the one
   action that did, PerformPut, is replaced below. *)
C ==
    INSTANCE Concrete WITH outbox <- network

SubmitExternal(ev) ==
    /\ C!SubmitExternal(ev)
    /\ UNCHANGED offers

SubmitInternal(name) ==
    /\ C!SubmitInternal(name)
    /\ UNCHANGED offers

Process(r) ==
    /\ C!Process(r)
    /\ UNCHANGED offers

PerformDone(r) ==
    /\ C!PerformDone(r)
    /\ UNCHANGED offers

PerformPutTimeout(r) ==
    /\ C!PerformPutTimeout(r)
    /\ UNCHANGED offers

(* The full swept document lands atomically. Its sends become ghost offers;
   the physical network is not touched by this storage operation. *)
PerformPutDocument(r) ==
    /\ r \in DOMAIN steps
    /\ steps[r].phase = "perform"
    /\ steps[r].pending /= << >>
    /\ LET e    == Head(steps[r].pending)
           rest == [steps EXCEPT ![r].pending = Tail(@)]
       IN  /\ e.tag = "PutDocument"
           /\ docs[C!OriginOf(steps[r].ev)] = steps[r].expect
           /\ docs'   = [docs EXCEPT ![C!OriginOf(steps[r].ev)] = e.body]
           /\ offers' = C!Deliver(offers, e.sends)
           /\ steps'  = rest
           /\ UNCHANGED <<timeouts, network, now>>

PerformMiss(r) ==
    /\ C!PerformMiss(r)
    /\ UNCHANGED offers

PerformDelTimeout(r) ==
    /\ C!PerformDelTimeout(r)
    /\ UNCHANGED offers

Perform(r) ==
    \/ PerformDone(r)
    \/ PerformPutTimeout(r)
    \/ PerformPutDocument(r)
    \/ PerformMiss(r)
    \/ PerformDelTimeout(r)

Crash(r) ==
    /\ C!Crash(r)
    /\ UNCHANGED offers

Post(sent, msg) ==
    { old \in sent : MsgKey(old) /= MsgKey(msg) } \cup {msg}

SendOffer(msg) ==
    /\ msg \in offers
    /\ offers'  = offers \ {msg}
    /\ network' = Post(network, msg)
    /\ UNCHANGED <<docs, timeouts, steps, now>>

DropOffer(msg) ==
    /\ msg \in offers
    /\ offers' = offers \ {msg}
    /\ UNCHANGED <<docs, timeouts, network, steps, now>>

Clock ==
    /\ C!Clock
    /\ UNCHANGED offers

Init ==
    /\ docs     = [o \in Origin |-> EmptyFn]
    /\ timeouts = EmptyFn
    /\ offers   = {}
    /\ network  = {}
    /\ steps    = EmptyFn
    /\ now      = 0

Next ==
    \/ \E ev \in ExternalEvent : SubmitExternal(ev)
    \/ \E name \in DOMAIN timeouts : SubmitInternal(name)
    \/ \E r \in DOMAIN steps : Process(r) \/ Perform(r) \/ Crash(r)
    \/ \E msg \in offers : SendOffer(msg) \/ DropOffer(msg)
    \/ Clock

Safety ==
    Init /\ [][Next]_vars

NowBound ==
    C!C_NowBound

VersionBound ==
    C!C_VersionBound

TypeOK ==
    /\ C!C_TypeOK
    /\ offers \subseteq OutEntry
    /\ \A a, b \in offers : MsgKey(a) = MsgKey(b) => a = b

DocumentWrite ==
    docs' /= docs

NetworkWrite ==
    network' /= network

SeparatedWrites ==
    ~(DocumentWrite /\ NetworkWrite)

THEOREM NextSeparatesDocumentAndNetwork ==
    Next => SeparatedWrites
PROOF
    BY DEF Next, SubmitExternal, SubmitInternal, Process, Perform,
           PerformDone, PerformPutTimeout, PerformPutDocument, PerformMiss,
           PerformDelTimeout, Crash, SendOffer, DropOffer, Clock,
           C!SubmitExternal, C!SubmitInternal, C!Process,
           C!PerformDone, C!PerformPutTimeout, C!PerformMiss,
           C!PerformDelTimeout, C!Crash, C!Clock,
           SeparatedWrites, DocumentWrite, NetworkWrite

=============================================================================
