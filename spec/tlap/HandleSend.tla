----------------------------- MODULE HandleSend -----------------------------
(* A concrete handler posts no sends. The queued outbox is the sweep's. *)
EXTENDS Concrete, TLAPS

Tags ==
    { "PromiseCreate", "PromiseSettle",
      "PromiseRegisterCallback", "PromiseRegisterListener",
      "TaskCreate", "TaskAcquire", "TaskFence",
      "TaskHeartbeat", "TaskSuspend", "TaskFulfill",
      "TaskRelease", "TaskHalt", "TaskContinue", "Timeout" }

LEMMA HandleSends ==
    ASSUME NEW ev, NEW doc, NEW t, ev.tag \in Tags
    PROVE  Handle(ev, doc, t).sends = << >>
PROOF
    <1>2. CASE ev.tag = "PromiseCreate"
        BY <1>2, Zenon DEF Handle, HandlePromiseCreate, Skip
    <1>3. CASE ev.tag = "PromiseSettle"
        BY <1>3, Zenon DEF Handle, HandlePromiseSettle, Skip
    <1>4. CASE ev.tag = "PromiseRegisterCallback"
        BY <1>4, Zenon DEF Handle, HandlePromiseRegisterCallback, Skip
    <1>5. CASE ev.tag = "PromiseRegisterListener"
        BY <1>5, Zenon DEF Handle, HandlePromiseRegisterListener, Skip
    <1>7. CASE ev.tag = "TaskCreate"
        BY <1>7, Zenon DEF Handle, HandleTaskCreate, Skip
    <1>8. CASE ev.tag = "TaskAcquire"
        BY <1>8, Zenon DEF Handle, HandleTaskAcquire, Skip
    <1>9. CASE ev.tag = "TaskFence"
        BY <1>9, Zenon DEF Handle, HandleTaskFence, Skip,
                            HandlePromiseCreate, HandlePromiseSettle
    <1>10. CASE ev.tag = "TaskHeartbeat"
        BY <1>10, Zenon DEF Handle, HandleTaskHeartbeat, Skip
    <1>11. CASE ev.tag = "TaskSuspend"
        BY <1>11, Zenon DEF Handle, HandleTaskSuspend, Skip
    <1>12. CASE ev.tag = "TaskFulfill"
        BY <1>12, Zenon DEF Handle, HandleTaskFulfill, Skip
    <1>13. CASE ev.tag = "TaskRelease"
        BY <1>13, Zenon DEF Handle, HandleTaskRelease, Skip
    <1>14. CASE ev.tag = "TaskHalt"
        BY <1>14, Zenon DEF Handle, HandleTaskHalt, Skip
    <1>15. CASE ev.tag = "TaskContinue"
        BY <1>15, Zenon DEF Handle, HandleTaskContinue, Skip
    <1>16. CASE ev.tag = "Timeout"
        BY <1>16 DEF Handle, Skip
    <1>17. QED
        BY <1>2, <1>3, <1>4, <1>5, <1>7, <1>8, <1>9, <1>10,
           <1>11, <1>12, <1>13, <1>14, <1>15, <1>16 DEF Tags

=============================================================================
