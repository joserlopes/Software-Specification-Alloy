module Ex2

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

fact {
    // All messages are in some of the three states
    always Msg = SentMsg + SendingMsg + PendingMsg
    // No Message can be in two different states
    always no (SentMsg & (SendingMsg + PendingMsg))
    always no (SendingMsg & (SentMsg + PendingMsg))
    always no (PendingMsg & (SentMsg + SendingMsg))
}

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
    // no sndr
    // No message has been sent yet, so no receivers
    no rcvrs
    // No node is queueing to become a member
    no qnxt
    // The outbox of each node contains it's own messages

    // Memebers are only the nodes that belong to the ring
    // maybe not needed
    all m: Member |
        m.(^nxt) = Member
    
    all n: Node |
        some n.outbox
    
    // For all messages msg.sndr = m iff msg in m.outbox
    all msg: Msg, n: Node |
        (msg.sndr = n) iff (msg in n.outbox)
    // // TODO: Ask if this is necessary
    // all n1, n2: Node | n1.outbox != n2.outbox
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

pred stutterRing[] {
    nxt' = nxt
    qnxt' = qnxt
    Leader' = Leader
    Member' = Member
    lnxt' = lnxt
    LQueue' = LQueue
}

pred stutterMessages[] {
    outbox' = outbox
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
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
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
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
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
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
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
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
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
    // All messages have been sent
    no SendingMsg

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
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
}

pred leaderPromotionMultiple[mFirst: Member] {
    // Pre

    one mFirst.~(Leader.lnxt)

    mFirst = Leader.~(Leader.lnxt)

    // All messages have been sent
    no SendingMsg
    // no PendingMsg & Leader.outbox

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
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
}

// m is the new Leader
pred leaderPromotion[] {
    some mFirst: Member | (
        leaderPromotionSingle[mFirst]
        ||
        leaderPromotionMultiple[mFirst]
    )
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
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
}

pred nonMemberExitNotTail[m: Member, n: Node] {
    // Pre

    // m has exactly one node on it's qnxt queue
    one n.~(m.qnxt)
    // n has to be a member of m's qnxt queue
    n in Node.(~(m.qnxt))
    // Some other node on m'x qnxt queue must be poiting to n
    some (m.qnxt).n
    // n can't be part of the Member ring
    n !in Member.(^nxt)

    // Post
    qnxt' = qnxt - (m->n->n.(m.qnxt)) - (m->n.~(m.qnxt)->n) + (m->n.~(m.qnxt)->m)

    // Frame

    nxt' = nxt
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

pred nonMemberExit[m: Member, n: Node] {
    nonMemberExitTail[m, n]
    ||
    nonMemberExitNotTail[m, n]
}

pred memberExitAux[m: Member, beforeM: Member] {
    // Pre

    // m is not in the LQueue
    m !in LQueue
    // m has no Nodes in it's lnxt queue
    no m.lnxt
    m = beforeM.nxt
    // TODO: All m's messages are sent
    no m.outbox 


    // Post
    
    // m is no longer a Member
    nxt' = nxt + (beforeM->m.nxt) - (m->m.nxt) - (beforeM->m)
    Member' = Member - m

    // Frame

    // Everything else remains the same
    qnxt' = qnxt
    outbox' = outbox
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    PendingMsg' = PendingMsg
}

// NOTE: This predicate can be done without the need for an auxiliary
// one, this just makes it more explicit
pred memberExit[m: Member] {
    some beforeM: Member | memberExitAux[m, beforeM]
}

pred broadcastInitialisation[msg: PendingMsg] {
    // Pre

    // Only the Leader can initialize the broadcast
    msg.sndr = Leader
    // Broadcast for this message hasn't yet started
    // msg in PendingMsg
    // Can only send messages from the outbox
    msg in Leader.outbox
    // Leader can't send a message to itself
    Leader.nxt != Leader
    
    // Post

    // Message is now Sending state
    PendingMsg' = PendingMsg - msg
    SendingMsg' = SendingMsg + msg
    // Swap outboxes
    outbox' = outbox - (Leader->msg) + (Leader.nxt->msg)
    // The next node has received the message
    rcvrs' = rcvrs + (msg->Leader.nxt)

    // Frame
    nxt' = nxt
    qnxt' = qnxt
    Leader' = Leader
    Member' = Member
    lnxt' = lnxt
    LQueue' = LQueue
    SentMsg' = SentMsg
}

pred messageRedirect[m: Member, msg: SendingMsg] {
    // Pre

    // m is not the Leader
    m != Leader
    // Can't redirect a message to the Leader. That's a case of broadcastTermination
    m.nxt != Leader
    // msg is in the outbox of m
    msg in m.outbox
    // Can only redirect messages sent from the Leader
    msg.sndr = Leader

    // Post

    // outbox' = outbox - (m.(~nxt)->msg) + (m.nxt->msg)
    outbox' = outbox - (m->msg) + (m.nxt->msg)
    // rcvrs' = rcvrs + (msg->m) + (msg->m.nxt)
    rcvrs' = rcvrs + (msg->m.nxt)

    // Frame
    nxt' = nxt
    qnxt' = qnxt
    Leader' = Leader
    Member' = Member
    lnxt' = lnxt
    LQueue' = LQueue
    PendingMsg' = PendingMsg
    SendingMsg' = SendingMsg
    SentMsg' = SentMsg
}

pred broadcastTerminationAux[msg: SendingMsg, mLast: Member] {
    // Pre

    // Leader has to be the sender of the message
    msg.sndr = Leader
    // mLast is the Member before Leader
    Leader = mLast.nxt
    // Message has to be present in the outbox of the Member before the Leader
    msg in mLast.outbox
    mLast in msg.rcvrs
    msg !in Leader.outbox

    // Post

    // Message is now sent
    SentMsg' = SentMsg + msg
    SendingMsg' = SendingMsg - msg
    // Message leaves the mLast's outbox
    outbox' = outbox - (mLast->msg)

    // Frame
    nxt' = nxt
    qnxt' = qnxt
    Leader' = Leader
    Member' = Member
    lnxt' = lnxt
    LQueue' = LQueue
    rcvrs' = rcvrs
    PendingMsg' = PendingMsg
}

pred broadcastTermination[msg: SendingMsg] {
    some mLast: Member | broadcastTerminationAux[msg, mLast]
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
    ||
    some m: Member, n: Node | nonMemberExit[m, n]
    ||
    some m: Member | memberExit[m]
    ||
    some msg: PendingMsg | broadcastInitialisation[msg]
    ||
    some m: Member, msg: SendingMsg | messageRedirect[m, msg]
    ||
    some msg: SendingMsg | broadcastTermination[msg]
}

pred system[] {
    init[]
    always trans[]
}

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
    // validSentMsg[]
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
}

pred validSentMsg[] {
    // 7.1 Outbox contains no sent messages
    no Node.outbox & SentMsg

    // 7.2 Sent messages have receivers
    some SentMsg
    implies
    some SentMsg.rcvrs

    // 7.3 Nodes cannot receive their own message
    no Msg.rcvrs & Msg.sndr
}


fun visualizeMemberQueues[]: Node->Node {
    Member.qnxt
}

fun visualizeLeaderQueues[]: Node->Node {
    Leader.lnxt
}

fun First[]: Node {
    Member.~(Member.qnxt)
}

fact {
    system[]
}

assert validSystem {
    system[]
    always validLoop[]
    always validMembershipQueue[]
    always validLeadershipQueue[]
    always validMsgs[]
}

check validSystem for 3 Node, 3 Msg
