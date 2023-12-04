//defining date
sig Date {}
//Defining Users
sig Username {}
abstract sig User{
	username :  Username,
} 
sig Educator extends User{}
sig Student extends User{
	collectedBadges : set Badge
}
//Defining team structure
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
//Defining Tournament and Tournament rankings
sig TournamentId{}
abstract  sig State{}
one sig Open extends State {}
one sig Close extends State{}
one sig Ongoing extends State{}
sig Points{}
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
	
//Defining Battle and Battle rankings
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
//Defining badge Structure
sig BadgeId{}
sig Badge {
	tournamentId:TournamentId,
	badgeId :BadgeId,
}

---------------------------------------------------
--Facts
---------------------------------------------------

//Tournament 

//grants the tournamentID is unique
fact uniqueTournamentId{
    all t1,t2:Tournament |t1!=t2 => t1.tournamentId != t2.tournamentId
}
//grants that the tournamentID exists only if exists a tournament with this id 
fact tournamentIdHasTournament{
	all ti : TournamentId | one t:Tournament | t.tournamentId = ti
}
//grants that the creator of the tournament is not in the collaborators list
fact creatorIsNotCollaborator{
    all t : Tournament| t.creator not in t.collaborators
}
//grants that all the battles in a tournament have the right tournament id
fact allBattlesHaveOneTournamentId{
    all t: Tournament, b:t.battles| b.tournamentId = t.tournamentId
}

//Battle

//grants thah a battke exists only in a tournament
fact battleExistsOnlyInATournament{
	all b: Battle |one t:Tournament | b in t.battles
}
//grants thaht the battleID is unique
fact uniqueBattleId{
    all b1,b2 : Battle| b1 != b2 => b1.battleId != b2.battleId
}
//grants that the battleID exists only if exists a battle with this id 
fact noBattleIdWithoutBattle{
	all bi:BattleId |one b:Battle| bi in b.battleId
}
//grants that the creator of a battle is part of the tournament 
fact battleCreatorIsInTournament{
	all t:Tournament, b: t.battles | (b.creator in t.collaborators) or ( b.creator=t.creator)
}
//grants that if a student is enrolled in a battle than he is a partecipant of the tournament
fact ifStudentInBattleThenInTournament{
	all t:Tournament, b:t.battles,s:Student| s in b.partecipants => s in t.partecipants 
}
//grants that a CodeKata exists only if it's the code of a battle
fact noCodekataWithoutBattle{
	all ck:CodeKata | one b: Battle | ck = b.code
}

//User

//grants that the username is unique
fact usernameIsUnique{
	all u1,u2 :User |u1 !=u2 => u1.username != u2.username 
}
//grants that a Username exists only if it's the username of an existing User
fact NoUsernameWithoutUser{
	all un :Username | one u : User | un = u.username
}

//Team

//grants that a team exists only in a battle 
fact teamExistsOnlyInOneBattle{
	all t: Team |one b:Battle | t in b.teams
}
//grants that a user can't join two teams in the same battle
fact NoSharedPlayers { 
  all b: Battle, t1, t2: b.teams |t1!=t2 => ((t1.members & t2.members) = none)
}
//grants that the teamID is unique 
fact uniqueTeamId{
    all b:Battle| all t1,t2 : b.teams| t1!=t2 =>t1.teamId != t2.teamId
}
//grants that a TeamId exists only if it's the id of an existing team
fact noTeamIdWithoutTeam{
	all ti:TeamId |one t:Team| ti in t.teamId
}
//grants that all the teams of a battle have the right battleID
fact allTeamsHaveTheRightBattleId{
    all b: Battle, t:b.teams|t.battleId = b.battleId
}
//grants that a team is composed with at least one student
fact noTeamWithoutStudents{
	all tm: Team | some s: Student| s in tm.members
}
//grants that all the students of a team are partecipants of the battle
fact allTeamStudentAreInBattle{
	all b: Battle, s:b.teams.members| s in b.partecipants
}
//grants that all the teams respect the limitations in size 
fact allTeamsRespectMaxMin{
	all b: Battle, t:b.teams | t.size <= b.maxTeamSize and t.size >= b.minTeamSize
}

//Badges

//grants that a Badge exists only if belongs to an existing tournament
fact badgeExistsOnlyInATournament{
	all b: Badge |one t:Tournament | b in t.badges 
}
//grants that the badgeId is unique 
fact uniqueBadgeId{
    all b1,b2 : Badge| b1 != b2 => b1.badgeId != b2.badgeId
}
//grants that a BadgeId exists only if it's the id of a Badge
fact noBadgeIdWithoutBadge{
	all bi:BadgeId |one b:Badge| bi in b.badgeId
}
//grants that a student that is not a partecipant of a tournament cannot have the tournament's badge 
fact StudentThatAreNotInATournamentCannotHaveItsBadges{
	all s: Student, t: Tournament |
    (s not in t.partecipants) implies not (one b: Badge | b in s.collectedBadges and b in t.badges)
}
//grants that if a tournament is closed there is at least a partecipants that have earned any tournament's badge
fact ifATournamentIsClosedSomeOfItsStudentsHaveItsBadge{
	all t:Tournament, bd:t.badges|t.state = Close => bd in t.partecipants.collectedBadges
}
//grants thath if a tournament isn't close there isn't any partecipant that have earned any tournament's badge
fact ifATournamentIsNotClosedAllItsBadgesAreNotAssigned{
	all t :Tournament, bd:t.badges|t.state != Close => bd not in t.partecipants.collectedBadges
}

//State

//grants that if a tournament is in OPEN state there isn't any battle in it 
fact ifTournamentIsOpenDontContainsBattles{
	all t:Tournament | t.state = Open => t.battles = none 
}
//grants that if a tournament is closed all the battles of this tournament are closed
fact ifTournamentIsCloseAllBattlesMustBeClose{
	all t:Tournament,b:t.battles | t.state = Close => b.state = Close
}

//Scores and LeaderBoards

//grants that the cardinality of a tournament leaderboard is equal to the number of partecipants of it
fact CardinalityCheckForTScores{
	all t:Tournament| #t.partecipants = #t.tournamentLeaderboard
}
//grants that the cardinality of a battle leaderboard is equal to the number of partecipants of it
fact CardinalityCheckForBScores{
	all b:Battle | #b.teams = #b.battleLeaderboard
}
//grants that the leaderboard of a tournament is only composed by partecipants of the tournament  
fact NoStudentEnrolledWithoutTScore{
	all t:Tournament,s:t.partecipants|one tlt :t.tournamentLeaderboard.student|s = tlt
}
//grants that the leaderboard of a battle is only composed by teams of the battle
fact NoTeamWithOutBScore{
	all b:Battle,t:b.teams |one blt : b.battleLeaderboard.team|t =blt
}
//grants that a tournament score exists only if it's in a tournament leaderboard  
fact everyTScoreBelongsToT{
	all ts : TournamentScore | one t:Tournament | ts in t.tournamentLeaderboard
}
//grants that a battle score exists only if it's in a battle leaderboard  
fact everyBScoreBelongsToB{
	all bs: BattleScore | one b:Battle | bs in b.battleLeaderboard
}

---------------------------------------------------
--Predicates
---------------------------------------------------


//The rules described in the following predicates don't belong strictly to the model
//however are usefull to underline the not trivial solution to rapresent the model,
//in this way we can observe clearly the structure of the model.

//ensures that there isn't any student that is not a partecipant of a tournament
pred allStudentEnrolled{
	all s:Student | s in Tournament.partecipants
}
//ensures that there isn't any educator that is not a partecipant of a tournament
pred allEducatorsInvolved{
	all e : Educator | (e in Tournament.creator ) or (e in Tournament.collaborators)
}
//ensures that every student partecipates in at least a battle
pred NofreeStudentInTournament{
	all t:Tournament, s:t.partecipants|one b: t.battles| s in b.partecipants
}
//ensures that every student partecipates in at least a member of a team
pred NofreeStudentInABattle{
	all b: Battle, s : b.partecipants| one t : b.teams | s in t.members
}


//WORLD GENERATION

// WORLD1 MULTITOURNAMENT AND MULTIBATTLE STRUCTURE


pred world1 {
	NofreeStudentInABattle
	NofreeStudentInTournament
	allEducatorsInvolved
	allStudentEnrolled
	#Tournament = 2
	#Battle = 2
	#Educator = 2
	#Student = 4
	#Badge = 0
	all t:Tournament  | one b:Battle | b in t.battles
	all b:Battle | some s:Student | s in b.partecipants
	
}
run world1 for 10

//WORLD2 SCORE SYSTEM AND TEAM STRUCTURE

pred world2 {
	NofreeStudentInABattle
	NofreeStudentInTournament
	allEducatorsInvolved
	allStudentEnrolled
	#Tournament = 1
	#Battle = 1
	#Educator = 1
	#Student = 7
	#Badge = 0
	#Team > 2
	
}
run world2 for 10

// BADGE MANAGEMENT AND ASSIGNMENT DUE TO TOURNAMENT STATE
pred world3 {
	NofreeStudentInABattle
	NofreeStudentInTournament
	allEducatorsInvolved
	allStudentEnrolled
	#Tournament = 2
	#Battle = 1
	#Educator = 1
	#Student = 2
	#Badge = 2
	one t:Tournament | t.state = Close
	one t:Tournament | t.state != Close
	all t:Tournament | one b:Badge | b in t.badges
	
}
run world3 for 10