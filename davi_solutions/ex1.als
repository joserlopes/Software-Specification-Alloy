sig Node {}

sig Member in Node {
    nxt: lone Member, // next member
    qnxt: Node -> lone Node, // node -> next in queue for membership
    // outbox: set Msg // set of messages to redirect
}

one sig Leader in Member {
    lnxt: Node -> lone Node // leader -> leader queue
}

sig LQueue in Member {} // set of nodes in leader queue


/*
    1. Forming the loop
*/

// 1.1 All members must have a nxt and be the nxt of someone
fact {
    Member = nxt.Member
    &&
    Member = Member.nxt
}

// 1.2 next cannot be reciprocal
fact {
    no (nxt & ~nxt)
}

// 1.3 Every member can reach every other one through nxt (loops)
fact {
    all m1, m2: Member |
        m1 in (m2.^nxt) && m2 in (m1.^nxt)
}

/*
    2. Membership queue
*/

// 2.1 No members in domain of Member.qnxt
fact {
    all m: Member |
        no (Member & m.qnxt.Node) 
}

// 2.2 Owner of the queue must appear once in its co-domain if the list is not empty
fact {
    all m: Member |
        some m.qnxt 
        implies
        (Member & Node.(m.qnxt)) = m
}

// 2.3 Nodes can only queue once
fact {
    all m: Member, n: Node |
        n !in (n.^(m.qnxt))
}

// 2.3 Each node is 'pointed to' only once (including owner)
fact {
    all m:Member, n1:Node |
        lone n2: Node | n1 in n2.(m.qnxt)
}

// 2.4 Each node in the queue can eventually reach the owner
fact {
    all m: Member |
        all n: Node |
            n in m.qnxt.Node 
            implies
            m in n.^(m.qnxt)
}

// 2.5 Non-member nodes can only appear in the queue of one member
fact {
    all n: Node - Member |
        lone m: Member | n in m.qnxt.Node
}


fun visualizeMemberQueues[]: Node->Node {
    Member.qnxt
}


/*
    3. Leadership queue
*/


// 3.1 LQueue has all members in Leaders queue
fact {
    all m: Member |
        m in Leader.lnxt.Node
        implies
        m in LQueue
}

// 3.2 No non-members or leader in domain of Leader.lnxt
fact {
    no (((Node-Member)+Leader) & Leader.lnxt.Node)
}

// 3.3 No non-members in the codomain of Leader.lnxt
fact {
    no ((Node-Member) & Node.(Leader.lnxt)) 
}

// 3.4 Owner of the queue must appear once in its co-domain if the list is not empty
fact {
    some Leader.lnxt 
        implies
    (Leader in Node.(Leader.lnxt))
}

// 3.5 Each member can only queue once 
fact {
    all m:Member |
        m in Leader.lnxt.Node
        implies
        one m & Leader.lnxt.Node
}

// 3.6 Each node is 'pointed to' only once (including owner)
fact {
    all m1:Member |
        lone m2: Node | m1 in m2.(Leader.lnxt)
}

// 3.7 Each node in the queue can eventually reach the leader
fact {
    all m: Member |
        m in Leader.lnxt.Node
        implies
        Leader in m.^(Leader.lnxt)
}

fun visualizeLeaderQueues[]: Node->Node {
    Leader.lnxt
}

run {
    #Member > 3
    #Leader > 0
    #Leader.lnxt.Node > 1
    some LQueue
    some n: Node | n in (Node-Member)
    some m: Member | m !in (Leader.lnxt.Node)
} for 12