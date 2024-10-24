open Ex2

/*
    Validating static model
*/

pred validLoop[]{
    // 1.1 All members must have a nxt and be the nxt of someone
    Member = nxt.Member
    Member = Member.nxt

    // 1.2 next cannot be reciprocal
    // no (nxt & ~nxt)
    
    // 1.3 Every member can reach every other one through nxt (loops)
    all m1, m2: Member |
        m1 in (m2.^nxt) && m2 in (m1.^nxt)
}

pred validMembershipQueue[]{
    // 2.1 No members in domain of Member.qnxt
    all m: Member |
        no (Member & m.qnxt.Node) 
    // 2.2 Owner of the queue must appear once in its co-domain if the list is not empty
    all m: Member |
        some m.qnxt 
        implies
        (Member & Node.(m.qnxt)) = m
    // 2.3 Nodes can only queue once
    all m: Member, n: Node |
        n !in (n.^(m.qnxt))
    // 2.4 Each node is 'pointed to' only once (including owner)
    all m:Member, n1:Node |
        lone n2: Node | n1 in n2.(m.qnxt)
    // 2.5 Each node in the queue can eventually reach the owner
    all m: Member |
        all n: Node |
            n in m.qnxt.Node 
            implies
            m in n.^(m.qnxt)
    // 2.6 Non-member nodes can only appear in the queue of one member
    all n: Node - Member |
        lone m: Member | n in m.qnxt.Node
}

pred validLeadershipQueue[]{

    // 3.1 LQueue has all members in Leaders queue
    all m: Member |
        m in Leader.lnxt.Node
        implies
        m in LQueue

    // 3.2 Leader is not in LQueue
    Leader !in LQueue

    // 3.3 No non-members or leader in domain of Leader.lnxt
    no (((Node-Member)+Leader) & Leader.lnxt.Node)

    // 3.4 No non-members in the codomain of Leader.lnxt
    no ((Node-Member) & Node.(Leader.lnxt)) 

    // 3.5 Owner of the queue must appear once in its co-domain if the list is not empty
    some Leader.lnxt 
        implies
    (Leader in Node.(Leader.lnxt))

    // 3.6 Each member can only queue once 
    all m:Member |
        m in Leader.lnxt.Node
        implies
        one m & Leader.lnxt.Node

    // 3.7 Each node is 'pointed to' only once (including owner)
    all m1:Member |
        lone m2: Node | m1 in m2.(Leader.lnxt)

    // 3.8 Each node in the queue can eventually reach the leader
    all m: Member |
        m in Leader.lnxt.Node
        implies
        Leader in m.^(Leader.lnxt)

}

pred validMsgs[]{
    // 4.0 redundant: no messages without status
    all m: Msg |
        m in SentMsg 
        || m in SendingMsg
        || m in PendingMsg

    // 4.1 Sent, Sending and Pending are disjoint
    disj[SentMsg, SendingMsg, PendingMsg]

    // Include all message-specific validations
    validPendingMsg[]
    validSendingMsg[]
    validSentMsg[]
}

pred validPendingMsg[]{
    // 5.1 Pending messages are in its sender's outbox
    // i.e. outbox contains own node's pending messages
    all n: Node, msg: PendingMsg |
        msg in n.outbox 
        <=>
        msg.sndr = n

    // 5.2 Pending messages have no receivers
    some PendingMsg
    implies 
    no PendingMsg.rcvrs
}

pred validSendingMsg[] {
    // 6.1 There can be one or zero sending message at a time
    // EDIT: there can
    // lone SendingMsg

    // 6.2 Sending messages have the current Leader as the sender

    some SendingMsg
    implies
    SendingMsg.sndr = Leader

    // 6.3 Sending Messages need to have at least some receiver
    some SendingMsg
    implies
    some SendingMsg.rcvrs

    // 6.4 Sending Messages need to be in one member's outbox
    some SendingMsg
    implies
    one n: Node |
        SendingMsg in n.outbox

    // 6.5 If node has a Sending message in its outbox, node is a member
    // issue here
    all n: Node, msg: SendingMsg |
        msg in n.outbox
        implies
        n in Member

    // // 6.6 If node has a Sending message in its outbox, it is in the receivers of the message
    all n: Node, msg: SendingMsg |
        msg in n.outbox
        implies
        n in (n.outbox).rcvrs


    // 6.7 Nodes cannot receive their own message
    all m: SendingMsg |
        no m.rcvrs & m.sndr
}
        

pred validSentMsg[] {
    // 7.1 Outbox contains no sent messages
    no Node.outbox & SentMsg

    // 7.2 Sent messages have receivers
    some SentMsg
    implies
    some SentMsg.rcvrs

    // // 7.3 Nodes cannot receive their own message
    all m: SentMsg |
        no m.rcvrs & m.sndr
}


assert validSystem {
    system[]
    always validLoop[]
    always validMembershipQueue[]
    always validLeadershipQueue[]
    always validMsgs[]
}

check validSystem for 3 Node, 3 Msg

/*
    Fairness predicates
*/


pred fairnessMemberApplication[] {
    all m: Node, n: Node |
        eventually always (m in Member && n != m && n !in Node.(~(Member.qnxt)) && n !in Member.(^nxt))
            implies
        (always eventually
            memberApplication[m, n])
}

pred fairnessMemberPromotion[] {
    all m: Node, nFirst: Node |
        eventually always (m in Member && nFirst = m.~(m.qnxt))
            implies
        (always eventually
            memberPromotion[m])
}

pred fairnessLeaderApplication[] {
    all m: Node |
        eventually always (m in Member && m != Leader && m !in LQueue)
            implies
        (always eventually
            leaderApplication[m])
}

pred fairnessLeaderPromotion[] {
    all mFirst: Node |
        eventually always ((mFirst in Member) && (mFirst = Leader.~(Leader.lnxt)) && (no (sndr.Leader & PendingMsg)) && (no SendingMsg))
            implies
        (always eventually
            leaderPromotion[])
}

pred fairnessBroadcastInitialisation[] {
    all msg: Msg |
        eventually always (msg.sndr = Leader && msg in PendingMsg && msg in Leader.outbox && Leader.nxt != Leader)
            implies
        (always eventually
            broadcastInitialisation[msg])
}

pred fairnessMessageRedirect[] {
    all m: Node, msg: Msg |
        eventually always (m in Member && msg in SendingMsg && m != Leader && m.nxt != Leader && msg in m.outbox && msg.sndr = Leader)
            implies
        (always eventually
            messageRedirect[m, msg])
}

pred fairnessBroadcastTermination[] {
    all msg: Msg, mLast: Node |
        eventually always (mLast in Member && msg in SendingMsg && msg.sndr = Leader && mLast.nxt = Leader && msg in mLast.outbox)
            implies
        (always eventually
            broadcastTermination[msg])
}

pred fairness[] {
    fairnessMemberApplication[]
    &&
    fairnessMemberPromotion[]
    &&
    fairnessLeaderApplication[]
    &&
    fairnessLeaderPromotion[]
    &&
    fairnessBroadcastInitialisation[]
    &&
    fairnessMessageRedirect[]
    &&
    fairnessBroadcastTermination[]
}

pred allBroadcastsTerminate[] {
    Msg = SentMsg
    // all msg: Msg |
    //     once msg in PendingMsg implies eventually msg in SentMsg
}

pred noExits[] {
    always no m: Member, n: Node | nonMemberExit[m, n]
    always no m: Member | memberExit[m]
}

fun visualizeMemberQueues[]: Node->Node {
    Member.qnxt
}

fun visualizeLeaderQueues[]: Node->Node {
    Leader.lnxt
}

run {
    fairness[] && #Node > 1
}

run {
    fairness[] && noExits[] && #Node > 1
} for 20 steps

assert weakFairness {
    (fairness[] && #Node > 1) implies (eventually allBroadcastsTerminate[])
}

assert strongFairness {
    (fairness[] && noExits[] && #Node > 1) implies (eventually allBroadcastsTerminate[])
}

check weakFairness

check strongFairness
