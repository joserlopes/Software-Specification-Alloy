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

fact {
    Member = nxt.Member // all members must have a next
    &&
    Member = Member.nxt // all members must have someone pointing to them
}

// next cannot be reciprocal
fact {
    all m1, m2: Member |
    m1.nxt = m2 
    implies
    m2.nxt != m1
}

// The member can be reached again
fact {
    all m: Member |
        m in (m.^nxt)
}

run { #Member=7 } for 10 // cant find instance with 8 members.. why? 
