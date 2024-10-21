open Ex2

pred fairnessMemberApplication[] {
    all m: Member, n: Node |
        eventually always (n != m && n !in Node.(~(Member.qnxt)) && n !in Member.(^nxt))
            implies
        (always eventually
            memberApplication[m, n])
}

pred fairnessMemberPromotion[] {
    all m: Member, nFirst: Node |
        eventually always (nFirst = m.~(m.qnxt))
            implies
        (always eventually
            memberPromotion[m])
}

pred fairnessLeaderApplication[] {
    all m: Member |
        eventually always (m != Leader && m !in LQueue)
            implies
        (always eventually
            leaderApplication[m])
}

pred fairnessLeaderPromotion[] {
    all mFirst: Member |
        eventually always (mFirst = Leader.~(Leader.lnxt) && (no SendingMsg))
            implies
        (always eventually
            leaderPromotion[])
}

pred fairnessBroadcastInitialisation[] {
    all msg: PendingMsg |
        eventually always (msg.sndr = Leader && msg in Leader.outbox && Leader.nxt != Leader)
            implies
        (always eventually
            broadcastInitialisation[msg])
}

pred fairnessMessageRedirect[] {
    all m: Member, msg: SendingMsg |
        eventually always (m != Leader && m.nxt != Leader && msg in m.outbox && msg.sndr = Leader)
            implies
        (always eventually
            messageRedirect[m, msg])
}

pred fairnessBroadcastTermination[] {
    all msg: SendingMsg, mLast: Member |
        eventually always (msg.sndr = Leader && Leader = mLast.nxt && msg in mLast.outbox)
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
    // Msg = SentMsg
    // all msg: Msg |
    //	once msg in SendingMsg implies eventually msg in SentMsg
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
    fairness[] && #Node > 1 && noExits[]
} for 14 steps

assert weakFairness {
    (fairness[] && #Node > 1) implies (eventually allBroadcastsTerminate[])
}

assert strongFairness {
    (fairness[] && noExits[] && #Node > 1) implies (eventually allBroadcastsTerminate[])
}

check weakFairness

check strongFairness