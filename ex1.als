sig Node {}

sig Member in Node {
    nxt: lone Member, // next member
    // qnxt: Node -> lone Node, // node -> next in queue for membership
    // outbox: set Msg // set of messages to redirect
}

one sig Leader in Member {
    // lnxt: Node -> lone Node // leader -> leader queue
}

// sig LQueue in Member {} // set of nodes in leader queue

// abstract sig Msg {
    // sndr: Node, // Sender node
    // rcvrs: set Node // Nodes messages was delivered
// }

// sig SentMsg, SendingMsg, PendingMsg extends Msg {}

// All members must have a nxt and be the nxt of someone
fact {
    Member = nxt.Member
    &&
    Member = Member.nxt
}

// next cannot be reciprocal
// TODO: Change this fact to point free notation
fact {
    all m1, m2: Member |
    m1.nxt = m2 
    implies
    m2.nxt != m1

    // Point free notation
    // no (nxt & ~nxt)
}

// All nodes of a member's must be non Members
fact {

}

// Every member can be reached again through nxt
// TODO: Change this fact to point free notation
fact {
    all m: Member |
        m in (m.^nxt)
}

// Every member can reach every other one through nxt
// TODO: Change this fact to point free notation
fact {
    all m1, m2: Member |
        m1 in (m2.^nxt)
}

// fun visualizeMemberQueues[]: Node -> lone Node {
//     Member.qnxt
// }

run { #Member=7 } for 10 // cant find instance with 8 members.. why? 
