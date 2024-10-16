sig Node {}

var sig Member in Node {
    var nxt: one Member,
    var qnxt : Node -> lone Node,
    var outbox: set Msg
}

var one sig Leader in Member {
    var lnxt: Node -> lone Node
}

var sig LQueue in Member {}

abstract sig Msg {
    sndr: Node, // This can't change right?
    var rcvrs: set Node
}

sig SentMsg, SendingMsg, PendingMsg extends Msg {}

pred init[] {
    // Only the leader is present
    one nxt
    Leader.nxt = Leader
    // No one is queueing to become the leader
    no lnxt
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
}

// m still has no Nodes in it's qnxt queue
pred memberApplicationEmpty[m: Member, n: Node] {
    // Pre

    // m can't be queueing on itself
    n != m
    // n cannot be part of any queue
    n !in Node.(~(Member.qnxt))
    // No one is queueing on m
    no m.qnxt
    // n can't be part of the Member ring
    n !in Member.(^nxt)

    // Post

    // n gets added to the end of m's qnxt queue
    // Which in this case is m itself
    qnxt' = qnxt + (m->n->m)

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

pred memberApplicationWithQnxt[m: Member, n: Node] {
    some nLast: Node | memberApplicationWithQnxtAux[m, n, nLast]
}

// m already has some Nodes in it's qnxt queue
pred memberApplicationWithQnxtAux[m: Member, n: Node, nLast: Node] {
    // Pre

    // m can't be queueing on itself
    n != m
    // n cannot be part of any queue
    n !in Node.(~(Member.qnxt))
    // nLast has to be a member of m's qnxt queue
    nLast in Node.(~(m.qnxt))
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

// Add n to the end of m's qnxt queue
pred memberApplication[m: Member, n: Node] {
    memberApplicationEmpty[m, n]
    ||
    memberApplicationWithQnxt[m, n]
}

// m only has one Node in it's qnxt queue
pred memberPromotionSingle[m: Member, n: Node] {
    // Pre

    // m has exactly one node on it's qnxt queue
    one m.qnxt
    // n is the first node on m's qnxt queue
    n = m.~(m.qnxt)

    // Post

    // n is now a Member
    Member' = Member + n
    // n gets inserted between m and m.nxt
    n.nxt' = m.nxt
    m.nxt' = n
    // n is no longer in m's qnxt queue
    qnxt' = qnxt - (m->n->m)

    // Frame

    // Evetything else remains the same
    outbox' = outbox
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
    // Only nodes n and m change their nxt
    all n1: Node - (n + m) | n1.nxt' = n1.nxt
}

// m already has some Nodes in it's qnxt queue
pred memberPromotionMultiple[m: Member, n: Node] {
    // Pre

    // m has someone on it's qnxt queue
    #m.qnxt > 1
    // n is the first node on m's qnxt queue
    n = m.~(m.qnxt)

    // Post

    // n is now a Member
    Member' = Member + n
    // n gets inserted between m and m.nxt
    n.nxt' = m.nxt
    m.nxt' = n
    // The new member is no longer part of qnxt
    qnxt' = qnxt - (m->n->m) 
    // The next node in m's qnxt queue is the new head of said queue
    qnxt' = qnxt - (m->n.~(m.qnxt)->n) 
    qnxt' = qnxt + (m->n.~(m.qnxt)->m)

    // Frame

    // Evetything else remains the same
    outbox' = outbox
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
    // Only nodes n and m change their nxt
    all n1: Node - (n + m) | n1.nxt' = n1.nxt
}

// n is the node to be inserted on the ring coming from m's qnxt queue
pred memberPromotion[m: Member, n: Node] {
    memberPromotionSingle[m, n]
    ||
    memberPromotionMultiple[m, n]
}

// Leader has no Member in it's qnxt queue
pred leaderApplicationEmpty[m: Member] {
    // Pre

    // The Leader can't be part of it's own lnxt queue
    m != Leader
    // No one is queueing to become a Leader
    no Leader.lnxt

    // Post
    // The head of the Leader's lnxt queue is m
    lnxt' = lnxt + (Leader->m->Leader)
    // Add m to LQueue
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

// Leader already has some Members in it's qnxt queue
pred leaderApplicationWithLnxt[m: Member] {
    some mLast: Member | leaderApplicationWithLnxtAux[m, mLast]
}

// Leader already has some Members in it's qnxt queue
pred leaderApplicationWithLnxtAux[m: Member, mLast: Member] {
    // Pre

    // m can't be queueing on itself
    m != Leader
    // n cannot already be in the LQueue
    m !in LQueue
    // mLast has to be a member of m's qnxt queue
    mLast in Member.(~(Leader.lnxt))
    // No other node can be pointing to nLast
    no (Leader.lnxt).mLast
    //n !in Member.(^nxt)

    // Post

    // m gets added to the end of Leaders's lnxt queue
    lnxt' = lnxt + (Leader->m->mLast)
    // Add m to LQueue
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

// Add m to the end of the Leader's lnxt queue
pred leaderApplication[m: Member] {
    leaderApplicationEmpty[m]
    ||
    leaderApplicationWithLnxt[m]
}

// Leader only has one Member in it's lnxt queue
pred leaderPromotionSingle[m: Member] {
    // Pre

    // m has exactly one node on it's qnxt queue
    one Leader.lnxt
    // n is the first node on m's qnxt queue
    m = Leader.~(Leader.lnxt)
    // No messages on sending state
    no SendingMsg

    // Post

    // m is now the Leader
    Leader' = m
    // m is no longer in the Leader's lnxt queue
    lnxt' = lnxt - (Leader->m->Leader)
    // Remove m from LQueue
    LQueue' = LQueue - m

    // Frame

    // Evetything else remains the same
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    Member' = Member
    rcvrs' = rcvrs
}

// Leader already has some Nodes in it's lnxt queue
pred leaderPromotionMultiple[m: Member] {
    // Pre

    // m has exactly one node on it's qnxt queue
    #lnxt > 1
    // n is the first node on m's qnxt queue
    m = Leader.~(Leader.lnxt)
    // No messages on sending state
    no SendingMsg

    // Post

    // m is now the Leader
    Leader' = m
    // The new leader is no longer part of lnxt
    lnxt' = lnxt - (Leader->m->Leader)
    // The next node in m's qnxt queue is the new head of said queue
    // The next node in the leader's lnxt queue is the new head of said queue
    lnxt' = lnxt - (Leader->m.~(Leader.lnxt)->m) 
    lnxt' = lnxt + (Leader->m.~(Leader.lnxt)->Leader)
    // Remove m from LQueue
    LQueue' = LQueue - m

    // Frame

    // Evetything else remains the same
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    Member' = Member
    rcvrs' = rcvrs
}

// m is the new Leader
pred leaderPromotion[m: Member] {
    leaderPromotionSingle[m]
    ||
    leaderPromotionMultiple[m]
}

pred trans[] {
    stutter[]
    ||
    some m: Member, n: Node | memberApplication[m, n]
    ||
    some m: Member, n: Node | memberPromotion[m, n]
    ||
    some m: Member | leaderApplication[m]
    ||
    some m: Member | leaderPromotion[m]
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

fact {
    system[]
}

run {
    eventually (#qnxt = 2)
}

run {
    eventually some m: Member, n: Node | memberPromotion[m, n]
}

run {
    eventually #lnxt > 1
    eventually (some m: Member | leaderApplication[m])
}

run trace1 {
    eventually #lnxt > 1
    eventually #qnxt > 1
    eventually some m: Member | leaderPromotion[m]
} for 5

run trace2 {
    eventually #lnxt > 1
    eventually #qnxt > 1
    eventually some m: Member | leaderPromotion[m]
} for 5