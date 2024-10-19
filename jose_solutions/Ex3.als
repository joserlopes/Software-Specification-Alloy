open Ex2

pred fairnessMemberApplication[] {
    all m: Member, n: Node |
        eventually always (n != m && n !in Node.(~(Member.qnxt)) && n !in Member.(^nxt))
            implies
        always eventually
            memberApplication[m, n]
}

pred fairnessMemberPromotion[] {
    all m: Member, nFirst: Node |
        eventually always (nFirst = m.~(m.qnxt))
            implies
        always eventually
            memberPromotion[m]
}

pred fairnessLeaderApplication[] {
    all m: Member |
        eventually always (m != Leader && m !in LQueue)
            implies
        always eventually
            leaderApplication[m]
}

pred fairnessLeaderPromotion[] {
    all mFirst: Member |
        eventually always (mFirst = Leader.~(Leader.lnxt) && (no SendingMsg & Leader.outbox) && (no PendingMsg & Leader.outbox))
            implies
        always eventually
            leaderPromotion[]
}

pred fairnessBroadcastInitialisation[] {
    all msg: PendingMsg |
        eventually always (msg.sndr = Leader && msg in Leader.outbox && Leader.nxt != Leader)
            implies
        always eventually
            broadcastInitialisation[msg]
}

pred fairnessMessageRedirect[] {
    all m: Member, msg: SendingMsg |
        eventually always (m != Leader && msg in m.outbox && msg.sndr = Leader)
            implies
        always eventually
            messageRedirect[m, msg]
}

pred fairnessBroadcastTermination[] {
    all msg: SendingMsg |
        eventually always (Leader in msg.rcvrs && msg.sndr = Leader && once msg !in Leader.outbox && msg in Leader.outbox)
            implies
        always eventually
            broadcastTermination[msg]
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
    //     once msg in SendingMsg implies eventually msg in SentMsg
}

pred noExits[] {
    all m: Member, n: Node | nonMemberExit[m, n]
    &&
    all m: Member | memberExit[m]
}

fun visualizeMemberQueues[]: Node->Node {
    Member.qnxt
}

fun visualizeLeaderQueues[]: Node->Node {
    Leader.lnxt
}

check weakFairness {
    (fairness[] && #Node > 1) implies (allBroadcastsTerminate[])
}

check strongFairness {
    (fairness[] && noExits[] && #Node > 1) implies (allBroadcastsTerminate[])
}
