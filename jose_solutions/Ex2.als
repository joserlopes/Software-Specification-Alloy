sig Node {}

sig Member in Node {
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

    // Post

    // n gets added to the end of m's qnxt list
    // Which in this case is m itself
    qnxt' = qnxt + (m->n->m)

    // Frame

    // Everything else remains the same
    nxt' = nxt
    outbox' = outbox
    Leader' = Leader
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

    // Post

    // n gets added to the end of m's qnxt list
    qnxt' = qnxt + (m->n->nLast)

    // Frame

    // Everything else remains the same
    nxt' = nxt
    outbox' = outbox
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
}

pred memberApplication[m: Member, n: Node] {
    memberApplicationEmpty[m, n]
    ||
    memberApplicationWithQnxt[m, n]
}

pred trans[] {
    stutter[]
    ||
    some m: Member, n: Node | memberApplication[m, n]
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
    eventually (#qnxt > 1)
}
