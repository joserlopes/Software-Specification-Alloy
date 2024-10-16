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
    // TODO: Talk about the messages
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
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    Leader' = Leader
    Member' = Member
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
}

pred memberApplicationEmpty[m: Member, n: Node] {
    // Pre

    // m can't be queueing on itself
    n != m
    // n cannot be part of any queue
    n !in Node.(~(Member.qnxt))
    // No one is poiting to m yet
    no m.qnxt
    // n !in Member.(^nxt)

    // Post

    // n gets added to the end of m's qnxt list
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
    //n !in Member.(^nxt)

    // Post

    // n gets added to the end of m's qnxt list
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
    memberApplicationEmpty[m, n]
    ||
    memberApplicationWithQnxt[m, n]
}

pred membermPromotionSingle[m: Member, n: Node] {
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
    qnxt' = qnxt - (m->n->m)

    // Frame

    // Evetything else remains the same
    outbox' = outbox
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
    all n1: Node - (n + m) | n1.nxt' = n1.nxt
}

pred membermPromotionMultiple[m: Member, n: Node] {
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
    // The next node in the qnxt queue is the new head
    qnxt' = qnxt - (m->n.~(m.qnxt)->n) 
    qnxt' = qnxt + (m->n.~(m.qnxt)->m)

    // Frame

    // Evetything else remains the same
    outbox' = outbox
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
    all n1: Node - (n + m) | n1.nxt' = n1.nxt
}

// n is the node to be inserted on the ring coming from m's qnxt queue
pred memberPromotion[m: Member, n: Node] {
    membermPromotionSingle[m, n]
    ||
    membermPromotionMultiple[m, n]
}

pred leaderApplicationEmpty[m: Member] {
    // Pre

    // Can't be part of my own queue of leaders
    m != Leader
    // 
    no Leader.lnxt

    // Post
    lnxt' = lnxt + (Leader->m->Leader)

    // Frame

    // Everything else remains the same
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    Leader' = Leader
    Member' = Member
    LQueue' = LQueue
    rcvrs' = rcvrs
}

pred leaderApplicationWithLnxt[m: Member] {
    some mLast: Member | leaderApplicationWithLnxtAux[m, mLast]
}

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

    //
    lnxt' = lnxt + (Leader->m->mLast)

    // Frame

    // Everything else remains the same
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    Leader' = Leader
    Member' = Member
    LQueue' = LQueue
    rcvrs' = rcvrs
}

pred leaderApplication[m: Member] {
    leaderApplicationEmpty[m]
    ||
    leaderApplicationWithLnxt[m]
}

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
    // 
    lnxt' = lnxt - (Leader->m->Leader)

    // Frame

    // Evetything else remains the same
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    Member' = Member
    LQueue' = LQueue
    rcvrs' = rcvrs
}

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
    // 
    lnxt' = lnxt - (Leader->m->Leader)
    // The next node in the lnxt queue is the new head
    lnxt' = lnxt - (Leader->m.~(Leader.lnxt)->m) 
    lnxt' = lnxt + (Leader->m.~(Leader.lnxt)->Leader)

    // Frame

    // Evetything else remains the same
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    Member' = Member
    LQueue' = LQueue
    rcvrs' = rcvrs
}

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

run {
    eventually #lnxt > 1
    eventually some m: Member | leaderPromotion[m]
}
