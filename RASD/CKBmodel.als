//defining date
sig Date {}

//defining users
sig Username {}
abstract sig User{
	username :  Username,
} 
sig Educator extends User{}
sig Student extends User{
	collectedBadges : set Badge
}

//defining team structure
sig TeamId{}
sig Team{
    	teamId: TeamId,
	battleId : BattleId,
	members : set Student,
	size:Int
}
{
	#members <= size
}

//defining tournament and tournament rankings
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
    	tournamentId : TournamentId,
	creator : one Educator,
	collaborators : set Educator,
	battles : set Battle,
	participants : set Student,
	subscriptionDeadline : Date,
	badges : set Badge,
	state : one State,
	tournamentRanking : set TournamentScore
}
	
//defining battle and battle rankings
sig BattleScore{
	team : Team,
	battlePoints : Points
}
sig CodeKata{}
sig BattleId{}
sig Battle{
    	battleId : BattleId,
    	tournamentId : TournamentId,
	creator : Educator,
	code : one CodeKata,
	participants : set Student,
	teams : set Team,
	maxTeamSize : Int,
	minTeamSize : Int,
	registrationDeadline: Date,
	submissionDeadline: Date,
	state : one State,
	battleRanking : set BattleScore
}
{
	maxTeamSize <=4
	minTeamSize > 0
	maxTeamSize >= minTeamSize
}

//defining badge structure
sig BadgeId{}
sig Badge {
	tournamentId : TournamentId,
	badgeId : BadgeId,
}

---------------------------------------------------
--Facts
---------------------------------------------------

//Tournament 

//ensures that the tournamentID is unique
fact uniqueTournamentId{
    	all t1,t2 : Tournament | t1!=t2 => t1.tournamentId != t2.tournamentId
}

//ensures that the tournamentID exists only if exists a tournament with this id 
fact tournamentIdHasTournament{
	all ti : TournamentId | one t:Tournament | t.tournamentId = ti
}

//ensures that the creator of the tournament is not in the collaborators list
fact creatorIsNotCollaborator{
    	all t : Tournament | t.creator not in t.collaborators
}

//ensures that all the battles in a tournament have the right tournament id
fact allBattlesHaveOneTournamentId{
    	all t : Tournament, b:t.battles| b.tournamentId = t.tournamentId
}

//Battle

//ensures that a battle exists only in a tournament
fact battleExistsOnlyInATournament{
	all b : Battle | one t:Tournament | b in t.battles
}

//ensures that the battleID is unique
fact uniqueBattleId{
    	all b1,b2 : Battle | b1 != b2 => b1.battleId != b2.battleId
}

//ensures that the battleID exists only if exists a battle with this id 
fact noBattleIdWithoutBattle{
	all bi : BattleId | one b:Battle | bi in b.battleId
}

//ensures that the creator of a battle is part of the tournament 
fact battleCreatorIsInTournament{
	all t : Tournament, b : t.battles | (b.creator in t.collaborators) or ( b.creator=t.creator)
}

//ensures that if a student is enrolled in a battle then he/she is a participant of the tournament
fact ifStudentInBattleThenInTournament{
	all t : Tournament, b : t.battles, s : Student| s in b.participants => s in t.participants 
}

//ensures that a CodeKata exists only if it is the code of a battle
fact noCodekataWithoutBattle{
	all ck : CodeKata | one b : Battle | ck = b.code
}

//User

//ensures that all the username are unique
fact usernameIsUnique{
	all u1,u2 : User | u1 !=u2 => u1.username != u2.username 
}

//ensures that a username exists only if it is the username of a user
fact NoUsernameWithoutUser{
	all un : Username | one u : User | un = u.username
}

//Team

//ensures that a team exists only in a battle 
fact teamExistsOnlyInOneBattle{
	all t : Team | one b : Battle | t in b.teams
}

//ensures that a user cannot join different teams in the same battle
fact NoSharedPlayers { 
  	all b : Battle, t1, t2: b.teams | t1!=t2 => ((t1.members & t2.members) = none)
}

//ensures that the teamID is unique 
fact uniqueTeamId{
    	all b : Battle| all t1,t2 : b.teams | t1!=t2 => t1.teamId != t2.teamId
}

//ensures that a TeamId exists only if it is the id of an existing team
fact noTeamIdWithoutTeam{
	all ti : TeamId | one t:Team | ti in t.teamId
}

//ensures that all the teams of a battle have the right battleID
fact allTeamsHaveTheRightBattleId{
    	all b : Battle, t : b.teams | t.battleId = b.battleId
}

//ensures that a team is composed of at least one student
fact noTeamWithoutStudents{
	all tm: Team | some s: Student | s in tm.members
}

//ensures that all the students of a team are participants of the battle
fact allTeamStudentAreInBattle{
	all b : Battle, s : b.teams.members | s in b.participants
}

//ensures that all the teams respect the limitations in size 
fact allTeamsRespectMaxMin{
	all b : Battle, t : b.teams | t.size <= b.maxTeamSize and t.size >= b.minTeamSize
}

//Badges

//ensures that a badge exists only if belongs to an existing tournament
fact badgeExistsOnlyInATournament{
	all b : Badge | one t : Tournament | b in t.badges 
}

//ensures that the badgeId is unique 
fact uniqueBadgeId{
    all b1,b2 : Badge | b1 != b2 => b1.badgeId != b2.badgeId
}

//ensures that a BadgeId exists only if it is the id of a Badge
fact noBadgeIdWithoutBadge{
	all bi : BadgeId | one b : Badge | bi in b.badgeId
}

//ensures that a student, who is not a participant of a tournament, cannot collects the tournament's badges
fact StudentThatAreNotInATournamentCannotHaveItsBadges{
	all s : Student, t : Tournament |
    (s not in t.participants) implies not (one b : Badge | b in s.collectedBadges and b in t.badges)
}

//ensures that if a tournament is closed there is at least one participant that have earned its badges
fact ifATournamentIsClosedSomeOfItsStudentsHaveItsBadge{
	all t : Tournament, bd : t.badges | t.state = Close => bd in t.participants.collectedBadges
}

//ensures that if a tournament is not closed there is not any participant that have earned its badges
fact ifATournamentIsNotClosedAllItsBadgesAreNotAssigned{
	all t : Tournament, bd : t.badges | t.state != Close => bd not in t.participants.collectedBadges
}

//State

//ensures that if a tournament is in open there are not any battles in it 
fact ifTournamentIsOpenDontContainsBattles{
	all t : Tournament | t.state = Open => t.battles = none 
}

//ensures that if a tournament is closed all the battles of this tournament are closed
fact ifTournamentIsCloseAllBattlesMustBeClose{
	all t : Tournament, b : t.battles | t.state = Close => b.state = Close
}

//Scores and Rankings

//ensures that the cardinality of a tournament ranking is equal to the number of participants in it
fact CardinalityCheckForTScores{
	all t : Tournament| #t.participants = #t.tournamentRanking
}

//ensures that the cardinality of a battle ranking is equal to the number of participants in it
fact CardinalityCheckForBScores{
	all b : Battle | #b.teams = #b.battleRanking
}

//ensures that the ranking of a tournament is only composed by participants of the tournament  
fact NoStudentEnrolledWithoutTScore{
	all t : Tournament, s : t.participants | one tlt :t.tournamentRanking.student|s = tlt
}

//ensures that the ranking of a battle is only composed by teams of the battle
fact NoTeamWithOutBScore{
	all b : Battle, t : b.teams |one blt : b.battleRanking.team|t =blt
}

//ensures that a tournament score exists only if it is in a tournament ranking
fact everyTScoreBelongsToT{
	all ts : TournamentScore | one t : Tournament | ts in t.tournamentRanking
}

//ensures that a battle score exists only if it is in a battle ranking
fact everyBScoreBelongsToB{
	all bs : BattleScore | one b : Battle | bs in b.battleRanking
}

---------------------------------------------------
--Predicates
---------------------------------------------------


//The rules described in the following predicates don't belong strictly to the model
//however are usefull to underline the not trivial solution to rapresent the model,
//in this way we can observe clearly the structure of the model.

//ensures that there isn't any student that is not a participant of a tournament
pred allStudentEnrolled{
	all s : Student | s in Tournament.participants
}

//ensures that there isn't any educator that is not a participant of a tournament
pred allEducatorsInvolved{
	all e : Educator | (e in Tournament.creator ) or (e in Tournament.collaborators)
}

//ensures that every student participates in at least a battle
pred NofreeStudentInTournament{
	all t : Tournament, s : t.participants | one b: t.battles | s in b.participants
}

//ensures that every student participates in at least a team
pred NofreeStudentInABattle{
	all b : Battle, s : b.participants | one t : b.teams | s in t.members
}


//WORLD GENERATION

//WORLD1: multi-tournament and multi-battle structure
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
	all b:Battle | some s:Student | s in b.participants
	
}
run world1 for 10

//WORLD2: score system and team structure
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

//WORLD3: badge management and assignment due to tournament state
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
