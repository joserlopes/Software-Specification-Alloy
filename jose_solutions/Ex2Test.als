sig Node {
  var outbox: set Msg
}

var sig Member in Node { 
 var nxt: one Node, 
 var qnxt : Node -> lone Node 
}

var one sig Leader in Member {
   var lnxt: Member -> lone Member
}

var sig LQueue in Member {}

sig Msg {
  sndr: Node, 
  var rcvrs: set Node 
}

var sig SentMsg, SendingMsg, PendingMsg in Msg {}

pred init[] {
    // Only the leader is present
    one nxt
    Leader.nxt = Leader
    // No one is queueing to become the leader
    no lnxt
    no LQueue
    // All messages are in the _pending_ state
    no SentMsg
    no SendingMsg
    no sndr
    no rcvrs
    // No node is queueing to become a member
    no qnxt

    // Memebers are only the nodes that belong to the ring
    all m: Member |
        m.(^nxt) = Member
}

pred stutter[] {
    // Nothing changes
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    Leader' = Leader
    Member' = Member
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
}

pred memberApplicationAux[m: Member, n: Node, nLast: Node] {
    // Pre

    // m can't be queueing on itself
    n != m
    // n cannot be part of any queue
    n !in Node.(~(Member.qnxt))
    // nLast is either a member of m's qnxt queue or the member itself
    nLast in Node.(~(m.qnxt)) || nLast = m
    // No other node can be pointing to nLast
    no (m.qnxt).nLast
    // n can't be part of the Member ring
    n !in Member.(^nxt)

    // Post

    // n gets added to the end of m's qnxt queue
    qnxt' = qnxt + (m->n->nLast)

    // Frame

    // Everything else remains the same
    nxt' = nxt
    outbox' = outbox
    Leader' = Leader
    Member' = Member
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
}

pred memberApplication[m: Member, n: Node] {
    some nLast: Node | memberApplicationAux[m, n, nLast]
}

pred memberPromotionSingle[m: Member, nFirst: Node] {
    // Pre

    // m has exactly one node on it's qnxt queue
    one m.qnxt
    // n is the first node on m's qnxt queue
    nFirst = m.~(m.qnxt)

    // Post

    // n is now a Member
    Member' = Member + nFirst
    // n gets inserted between m and m.nxt
    nxt' = nxt - (m->m.nxt) + (m->nFirst) + (nFirst->m.nxt)
    // n is no longer in m's qnxt queue
    qnxt' = qnxt - (m->nFirst->m)

    // Frame

    // Evetything else remains the same
    outbox' = outbox
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
}

// m already has some Nodes in it's qnxt queue
pred memberPromotionMultiple[m: Member, nFirst: Node] {
    // Pre

    // n is not the last Node on m's qnxt queue
    one nFirst.~(m.qnxt)
    // n is the first node on m's qnxt queue
    nFirst = m.~(m.qnxt)

    // Post

    // n is now a Member
    Member' = Member + nFirst
    // n gets inserted between m and m.nxt
    nxt' = nxt - (m->m.nxt) + (m->nFirst) + (nFirst->m.nxt)
    // The new member is no longer part of qnxt
    // n is no longer part of m's qnxt queue
    // The next node in m's qnxt queue is the new head of said queue
    qnxt' = qnxt - (m->nFirst->m) - (m->nFirst.~(m.qnxt)->nFirst) + (m->nFirst.~(m.qnxt)->m)

    // Frame

    // Evetything else remains the same
    outbox' = outbox
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
}

// n is the node to be inserted on the ring coming from m's qnxt queue
pred memberPromotion[m: Member] {
    some nFirst: Node | (
        memberPromotionSingle[m, nFirst]
        ||
        memberPromotionMultiple[m, nFirst]
    )
}

pred leaderApplicationAux[m: Member, mLast: Member] {
    // Pre

    // Leader can't be queueing on itself
    m != Leader
    // m is not part of the Leader Queue
    m !in LQueue
    // mLast is either a member of LQueue of the Leader itself
    (mLast in LQueue) || mLast = Leader
    // No other member can be poiting to mLast
    no (Leader.lnxt).mLast

    // Post

    // m gest added to the end of the Leader's lxnt queue
    lnxt' = lnxt + (Leader->m->mLast)
    LQueue' = LQueue + m

    // Frame

    // Everything else remains the same
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    Leader' = Leader
    Member' = Member
    rcvrs' = rcvrs
}

pred leaderApplication[m: Member] {
    some mLast: Member | leaderApplicationAux[m, mLast]
}

// Leader only has one Member in it's lnxt queue
pred leaderPromotionSingle[mFirst: Member] {
    // Pre

    // LQueue has exactly one Member
    one LQueue
    // TODO: Is this necessary??
    // mFirst is the first node on LQueue
    mFirst = Leader.~(Leader.lnxt)

    no SendingMsg
    no PendingMsg

    // Post
    // mFirst is now the Leader
    Leader' = /*Leader*/ mFirst
    // mFirst is no longer part of LQueue
    lnxt' = lnxt - (Leader->mFirst->Leader)
    // Remove m from LQueue
    LQueue' = LQueue - mFirst

    // Evetything else remains the same
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    Member' = Member
    rcvrs' = rcvrs
}

pred leaderPromotionMultiple[mFirst: Member] {
    // Pre

    one mFirst.~(Leader.lnxt)

    mFirst = Leader.~(Leader.lnxt)

    no SendingMsg
    no PendingMsg

    // Post

    lnxt' = lnxt - (Leader->mFirst->Leader) - (Leader->mFirst.~(Leader.lnxt)->mFirst) + (mFirst->mFirst.~(Leader.lnxt)->mFirst)
    Leader' = mFirst
    LQueue' = LQueue - mFirst

    // Frame
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    Member' = Member
    rcvrs' = rcvrs
}

// m is the new Leader
pred leaderPromotion[] {
    some mFirst: Member | (
        leaderPromotionSingle[mFirst]
        ||
        leaderPromotionMultiple[mFirst]
    )
}

// TODO: This one is going to be quite hard!!
pred memberExit[m: Member] {
    // Pre

    // m is not the Leader
    m !in Leader
}

pred nonMemberExitTail[m: Member, n: Node] {
    // Pre

    // m has exactly one node on it's qnxt queue
    some m.qnxt
    // n has to be a member of m's qnxt queue
    n in Node.(~(m.qnxt))
    // No other node can be pointing to n (n is the last element of m's qnxt queue)
    no (m.qnxt).n
    // n can't be part of the Member ring
    n !in Member.(^nxt)

    // Post
    qnxt' = qnxt - (m->n->n.(m.qnxt))

    // Frame

    nxt' = nxt
    outbox' = outbox
    Leader' = Leader
    Member' = Member
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
}

pred nonMemberExitNotTail[m: Member, n: Node] {
    // Pre

    // m has exactly one node on it's qnxt queue
    #m.qnxt > 1
    // n has to be a member of m's qnxt queue
    n in Node.(~(m.qnxt))
    // Some other node on m'x qnxt queue must be poiting to n
    some (m.qnxt).n
    // n can't be part of the Member ring
    n !in Member.(^nxt)

    // Post
    qnxt' = qnxt - (m->n->n.(m.qnxt))

    qnxt' = qnxt - (m->n.~(m.qnxt)->n) 
    qnxt' = qnxt + (m->n.~(m.qnxt)->m)

    // Frame

    nxt' = nxt
    outbox' = outbox
    Leader' = Leader
    Member' = Member
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
}

pred nonMemberExit[m: Member, n: Node] {
    nonMemberExitTail[m, n]
    ||
    nonMemberExitNotTail[m, n]
}

pred trans[] {
    stutter[]
    ||
    some m: Member, n: Node | memberApplication[m, n]
    ||
    some m: Member | memberPromotion[m]
    ||
    some m: Member | leaderApplication[m]
    ||
    leaderPromotion[]
}

pred system[] {
    init[]
    &&
    always trans[]
}

fun visualizeMemberQueues[]: Node->Node {
    Member.qnxt
}

fun visualizeLeaderQueues[]: Node->Node {
    Leader.lnxt
}

fun Teste[]: Node {
    Member.~(Member.qnxt)
}

fact {
    system[]
}

run {
    eventually (#qnxt > 3)
} for 7

run memberPromotion {
    eventually (#qnxt > 2)
    eventually (#Member > 2)
} for 5

run memberPromotionSingle {
    eventually (some m: Member, nFirst: Node | memberPromotionSingle[m, nFirst])
} for 6

run memberPromotionMultiple {
    eventually (some m: Member, nFirst: Node | memberPromotionMultiple[m, nFirst])
} for 6

// run nonMemberExitAndLeaderPromotion {
//     eventually #qnxt > 1
//     eventually #lnxt > 1
//     eventually some m: Member, n: Node | nonMemberExit[m, n]
//     eventually some m: Member | leaderPromotion[m]
// }

run leaderPromotion {
    eventually leaderPromotion[]
}

run leaderPromotionMultiple {
    eventually some mFirst: Member | leaderPromotionMultiple[mFirst]
}

run leaderApplication {
    eventually #LQueue > 2
    // eventually (some m: Member | leaderApplication[m])
} for 6 but 5 Node

// run trace1 {
//     eventually #lnxt > 1
//     eventually #qnxt > 1
//     eventually some m: Member | leaderPromotion[m]
// } for 5

// run trace2 {
//     eventually #lnxt > 1
//     eventually #qnxt > 1
//     eventually some m: Member | leaderPromotion[m]
// } for 5
