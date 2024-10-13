sig Node {}

sig Member in Node {
    // nxt: lone Member, // next member
    qnxt: Node -> lone Node, // node -> next in queue for membership
    // outbox: set Msg // set of messages to redirect
}

fun nodesInQueue[m: Member]: set Node {
    {m.qnxt.Node}
}

// Queue is acyclic
// fact {
//     all m: Member |
//         all n: Node |
//         n !in n.^(m.qnxt)

// }

// No members in domain of Member.qnxt
fact {
    all m: Member |
        no (Member & m.qnxt.Node) 
}

// Owner of the queue must appear once in its co-domain if the list is not empty
fact {
    all m: Member |
        some m.qnxt 
        implies
        (Member & Node.(m.qnxt)) = m
}

// Nodes can only queue once
fact {
    all m: Member, n: Node |
        n !in (n.^(m.qnxt))
}

// Queue only points to the member once. i.e. only one node points to it.
fact {
    all m: Member |
        lone n: Node | m in n.(m.qnxt)
}

// Each node is pointed only once
fact {
    all m:Member, n1:Node |
        lone n2: Node | n1 in n2.(m.qnxt)

}

// Each node in the queue can eventually reach the owner
fact {
    all m: Member |
        all n: Node |
            n in m.qnxt.Node implies m in n.^(m.qnxt)
}

// Non-member nodes can only appear in the queue of one member
fact {
    all n: Node - Member |
        lone m: Member | n in m.qnxt.Node
}

// Nodes in every qnxt can't be Members
// fact {
//     all m1: Member |
//         no (Member & m1.qnxt.Member)
// }

// 1.2 next cannot be reciprocal
// fact {
//     all m: Member |
//         no (m.qnxt & ~(m.qnxt))
// }

// 1.3 Nodes can be in one member queue

fun visualizeMemberQueues[]: Node->Node {
    Member.qnxt
}

run {
    #Member > 1
    all m: Member | #nodesInQueue[m] >= 2
} for 10
