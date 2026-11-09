-------------------------- MODULE DirectProtocol --------------------------
(***************************************************************************)
(* A no-sweep protocol. A document action performs exactly one due item or *)
(* one request handler. Due actions publish messages to the ghost `offers`  *)
(* set; only SendOffer changes `network`, and an offer may instead be       *)
(* dropped. Thus document storage and the best-effort network are separate. *)
(***************************************************************************)
EXTENDS Requests

VARIABLES
    objects,
    offers,
    network,
    now

vars ==
    <<objects, offers, network, now>>

(* Reuse the already checked protocol functions, but interpret its outbox as
   a set of messages offered to the network. It is not the network itself. *)
A ==
    INSTANCE Abstract WITH outbox <- offers

DocState(os, pending) ==
    [objects |-> os, offers |-> pending]

CurrentDoc ==
    DocState(objects, offers)

(* Exactly one due item. A!Due1 may update both the document and `offers`;
   the latter is ghost bookkeeping and is not a network write. *)
DueDocAfter(st, t) ==
    { DocState(nxt.objects, nxt.outbox) :
        nxt \in A!Due1(st.objects, st.offers, t) }

(* Exactly one client handler. Handlers do not publish messages. *)
HandlerDocAfter(st, t) ==
    { DocState(os, st.offers) :
        os \in A!Handled(st.objects, t) }

DirectDocAfter(st, t) ==
    DueDocAfter(st, t) \cup HandlerDocAfter(st, t)

DirectDocumentAt(t) ==
    \E nxt \in DirectDocAfter(CurrentDoc, t) :
        /\ objects' = nxt.objects
        /\ offers'  = nxt.offers
        /\ UNCHANGED <<network, now>>

DirectDocument ==
    \E t \in 0 .. now : DirectDocumentAt(t)

(* `network` records the latest observed message for each protocol key. This
   is deliberately best effort: an offer may be sent, dropped, or retained. *)
Post(sent, msg) ==
    { old \in sent : MsgKey(old) /= MsgKey(msg) } \cup {msg}

SendOffer(msg) ==
    /\ msg \in offers
    /\ offers'  = offers \ {msg}
    /\ network' = Post(network, msg)
    /\ UNCHANGED <<objects, now>>

DropOffer(msg) ==
    /\ msg \in offers
    /\ offers' = offers \ {msg}
    /\ UNCHANGED <<objects, network, now>>

Clock ==
    /\ now' = now + 1
    /\ UNCHANGED <<objects, offers, network>>

Init ==
    /\ objects = EmptyFn
    /\ offers  = {}
    /\ network = {}
    /\ now     = 0

Next ==
    \/ DirectDocument
    \/ \E msg \in offers : SendOffer(msg) \/ DropOffer(msg)
    \/ Clock

Safety ==
    Init /\ [][Next]_vars

NowBound ==
    now <= MaxTime

VersionBound ==
    \A i \in DOMAIN objects : objects[i].task.version <= MaxVersion

TypeOK ==
    /\ now \in Time
    /\ DOMAIN objects \subseteq Id
    /\ offers \subseteq OutEntry
    /\ network \subseteq OutEntry
    /\ \A a, b \in offers : MsgKey(a) = MsgKey(b) => a = b
    /\ \A a, b \in network : MsgKey(a) = MsgKey(b) => a = b

DocumentWrite ==
    objects' /= objects

NetworkWrite ==
    network' /= network

SeparatedWrites ==
    ~(DocumentWrite /\ NetworkWrite)

THEOREM NextSeparatesDocumentAndNetwork ==
    Next => SeparatedWrites
PROOF
<1>1. CASE DirectDocument
    BY <1>1 DEF DirectDocument, DirectDocumentAt,
                  SeparatedWrites, DocumentWrite, NetworkWrite
<1>2. CASE \E msg \in offers : SendOffer(msg) \/ DropOffer(msg)
    BY <1>2 DEF SendOffer, DropOffer, SeparatedWrites,
                  DocumentWrite, NetworkWrite
<1>3. CASE Clock
    BY <1>3 DEF Clock, SeparatedWrites, DocumentWrite, NetworkWrite
<1>4. QED
    BY <1>1, <1>2, <1>3 DEF Next

=============================================================================
