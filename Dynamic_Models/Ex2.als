sig Node {}

sig Member in Node {
    nxt: lone Member,
    qnxt : Node -> lone Node,
    outbox: set Msg
}

one sig Leader in Member {
    lnxt: Node -> lone Node
}

sig LQueue in Member {}

abstract sig Msg {
    sndr: Node,
    rcvrs: set Node
}

sig SentMsg, SendingMsg, PendingMsg extends Msg {}

pred init[] {
    // Only the leader is present
    one nxt
    Leader.nxt = Leader
    no lnxt
    #Member = 1
    // All messages are in the _pending_ state
    no SentMsg
    no SendingMsg

    // No node is queueing to become a member
    no qnxt
}

pred stutter[] {

}

pred trans[] {
    stutter[]
}

pred system[] {
    init[]
    &&
    always trans[]
}

fun visualizeMemberQueues[]: Node->Node {
    Member.qnxt
}

fact {
    system[]
}

run {
    
}
