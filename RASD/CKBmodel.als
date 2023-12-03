--QUESTIONE APERTA LEVIAMO TUTTI GLI ID E COLLEGHIAMO DIRETTAMENTE LE SIG 
--Questione Aperta FORZE è POSSIBILE PULIRE IL DIAGRAMMA DA ALCUNE FRECCE ANCORA NON SO COME 
sig Date {
}
abstract  sig State{}
one sig Open extends State {}
one sig Close extends State{}
one sig Ongoing extends State{}

sig Username {}
sig TournamentId{}
sig TournamentScore{
	student : Student,
	tournamentPoints : Points
}
sig Tournament {
    tournamentId: TournamentId,
	creator : one Educator,
	collaborators : set Educator,
	battles : set Battle,
	partecipants : set Student,
	subscriptionDeadline : Date,
	badges: set Badge,
	state :one State,
	tournamentLeaderboard: set TournamentScore

	
}
	
abstract sig User{
	username :  Username,
} 
sig Points{}
sig Student extends User{
	collectedBadges : set Badge
}
sig Educator extends User{}
sig TeamId{}
sig Team{
    teamId: TeamId,
	battleId : BattleId,
	members : set Student,
	size:Int
}
{
	#members <=size
}
sig BattleScore{
	team : Team,
	battlePoints : Points
}
sig CodeKata{}
sig BattleId{}
sig Battle{
    battleId: BattleId,
    tournamentId: TournamentId,
	creator : Educator,
	code : one CodeKata,
	partecipants : set Student,
	teams : set Team,
	maxTeamSize : Int,
	minTeamSize : Int,
	registrationDeadline: Date,
	submissionDeadline: Date,
	state : one State,
	battleLeaderboard: set BattleScore
}
{
	maxTeamSize <=4
	minTeamSize > 0
	maxTeamSize >= minTeamSize
}
sig BadgeId{}
sig Badge {
	tournamentId:TournamentId,
	badgeId :BadgeId,
}

---------------------------------------------------
--Facts
---------------------------------------------------

--Tournament



fact uniqueTournamentId{
    all t1,t2:Tournament |t1!=t2 => t1.tournamentId != t2.tournamentId
}
fact tournamentIdHasTournament{
	all ti : TournamentId | one t:Tournament | t.tournamentId = ti
}

fact creatorIsNotCollaborator{
    all t : Tournament| t.creator not in t.collaborators
}
fact allBattlesHaveOneTournamentId{
    all t: Tournament, b:t.battles| b.tournamentId = t.tournamentId
}

--Battle

fact battleExistsOnlyInATournament{
	all b: Battle |one t:Tournament | b in t.battles
}
fact uniqueBattleId{
    all b1,b2 : Battle| b1 != b2 => b1.battleId != b2.battleId
}
fact noBattleIdWithoutBattle{
	all bi:BattleId |one b:Battle| bi in b.battleId
}
fact battleCreatorIsInTournament{
	all t:Tournament, b: t.battles | (b.creator in t.collaborators) or ( b.creator=t.creator)
}
fact ifStudentInBattleThenInTournament{
	all t:Tournament, b:t.battles,s:Student| s in b.partecipants => s in t.partecipants 
}
fact noCodekataWithoutBattle{
	all ck:CodeKata | one b: Battle | ck = b.code
}
--User

fact usernameIsUnique{
	all u1,u2 :User |u1 !=u2 => u1.username != u2.username 
}
fact NoUsernameWithoutUser{
	all un :Username | one u : User | un = u.username
}

--Team

fact teamExistsOnlyInOneBattle{
	all t: Team |one b:Battle | t in b.teams
}
fact NoSharedPlayers { 
  all b: Battle, t1, t2: b.teams |t1!=t2 => ((t1.members & t2.members) = none)
}
fact uniqueTeamId{
    all b:Battle| all t1,t2 : b.teams| t1!=t2 =>t1.teamId != t2.teamId
}
fact noTeamIdWithoutTeam{
	all ti:TeamId |one t:Team| ti in t.teamId
}
fact allTeamsHaveTheRightBattleId{
    all b: Battle, t:b.teams|t.battleId = b.battleId
}
fact noTeamWithoutStudents{
	all tm: Team | some s: Student| s in tm.members
}
fact allTeamStudentAreInBattle{
	all b: Battle, s:b.teams.members| s in b.partecipants
}
fact allTeamsRespectMaxMin{
	all b: Battle, t:b.teams | t.size <= b.maxTeamSize and t.size >= b.minTeamSize
}
--Badges
fact badgeExistsOnlyInATournament{
	all b: Badge |one t:Tournament | b in t.badges 
}
fact uniqueBadgeId{
    all b1,b2 : Badge| b1 != b2 => b1.badgeId != b2.badgeId
}
fact noBadgeIdWithoutBadge{
	all bi:BadgeId |one b:Badge| bi in b.badgeId
}
fact StudentThatAreNotInATournamentCannotHaveItsBadges{
	all s: Student, t: Tournament |
    (s not in t.partecipants) implies not (one b: Badge | b in s.collectedBadges and b in t.badges)
}
fact ifATournamentIsClosedSomeOfItsStudentsHaveItsBadge{
	all t:Tournament, bd:t.badges|t.state = Close => bd in t.partecipants.collectedBadges
}
fact ifATournamentIsNotClosedAllItsBadgesAreNotAssigned{
	all t :Tournament, bd:t.badges|t.state != Close => bd not in t.partecipants.collectedBadges
}

-- State
fact ifTournamentIsOpenDontContainsBattles{
	all t:Tournament | t.state = Open => t.battles = none 
}
fact ifTournamentIsCloseAllBattlesMustBeClose{
	all t:Tournament,b:t.battles | t.state = Close => b.state = Close
}
--Scores and LeaderBoards
fact CardinalityCheckForTScores{
	all t:Tournament| #t.partecipants = #t.tournamentLeaderboard
}
fact CardinalityCheckForBScores{
	all b:Battle | #b.teams = #b.battleLeaderboard
}
fact NoStudentEnrolledWithoutTScore{
	all t:Tournament,s:t.partecipants|one tlt :t.tournamentLeaderboard.student|s = tlt
}
fact NoTeamWithOutBScore{
	all b:Battle,t:b.teams |one blt : b.battleLeaderboard.team|t =blt
}
fact everyTScoreBelongsToT{
	all ts : TournamentScore | one t:Tournament | ts in t.tournamentLeaderboard
}
fact everyBScoreBelongsToB{
	all bs: BattleScore | one b:Battle | bs in b.battleLeaderboard
}
--LE SEGUENTI NON SONO REGOLE DELLA STRUTTURA MA SERVONO A OSSERVARE IL SISTEMA IN SITUAZIONI INTERESSANTI
--Battles
fact NofreeStudentInABattle{
	all b: Battle, s : b.partecipants| one t : b.teams | s in t.members
}
--Students
fact allStudentEnrolled{
	all s:Student | s in Tournament.partecipants
}
--Educators 

fact allEducatorsInvolved{
	all e : Educator | (e in Tournament.creator ) or (e in Tournament.collaborators)
}


--Tournament
fact NofreeStudentInTournament{
	all t:Tournament, s:t.partecipants|one b: t.battles| s in b.partecipants
}






---------------------------------------------------
--Predicates
---------------------------------------------------
pred Cons {
	#Tournament = 1
	#Battle = 1
	#Educator = 1
	#Student = 5
	#Badge = 0
	#Team =2
	#Points >6
	one t:Tournament | t.state = Close
}
run Cons for 10





