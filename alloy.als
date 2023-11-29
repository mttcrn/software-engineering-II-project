sig Date {}
sig Time {}
sig DateTime{
	date : Date,
	time : Time
}


sig Username {}
sig Email {}
sig Name {}
sig Surname {}
sig Password{}

sig Test{}
sig Evaluator{
    battle : Battle,
    tests: some Test,
}

sig TournamentScore{
    name : TournamentName,
    score: Int,
}

abstract sig User{
	username : Username,
	email : Email,
	name : Name,
	surname : Surname,
	password : Password
} 

sig Student extends User{
    earnedBadges: set Badge,
    battlesWon : Int,
    tournamentScores: set TournamentScore,
}
sig Educator extends User{}
sig Team{
    teamId: Int,
	members : some Student,
    battleId : Int,
}


sig CodeKata{}
abstract sig State{}
one sig Open extends State{}
one sig Close extends State{}

sig BattleName{}
sig Battle{
    battleId: Int,
    tournamentId: one Int,
	name :BattleName,
	creator : one Educator,
	registrationDeadline : DateTime,
	submissionDeadline : DateTime,
	code : one CodeKata,
	teams : set Team,
	maxTeamSize :Int,
	minTeamSize:Int,
	state : one State,
    evaluator: Evaluator
}

sig BadgeName{}
sig Variable{}
sig Rule{}
sig Badge {
    badgeId: Int,
    title: BadgeName , 
    description : String,
    variables: set Variable,
    rules: set Rule,
    tournament: one Tournament
}


sig TournamentName{}
sig Tournament {
    tournamentId: Int,
	subscriptionDeadline : DateTime,
	creator :one Educator,
	name : TournamentName,
	collaborators : set Educator,
	battles : some Battle,
	partecipants : some Student,
	isClosed : one State,
	badges : set Badge
}	
	
---------------------------------------------------
--Facts
---------------------------------------------------

--Tournament

fact tournamentNameAreUnique{
	no disj t1,t2 : Tournament  | t1.name = t2.name
}

fact noTournamentNameWithoutTournament{
	all tn: TournamentName | one t:Tournament | t.name = tn
}

fact creatorIsInEducators{
	all t : Tournament | t.creator in t.collaborators
}
//penso vada bene ma attendo conferma
fact uniqueBadgesInTournament{
    no disj b1,b2: Tournament.badges | b1= b2
}

fact uniqueTournamentId{
    no disj t1,t2:Tournament | t1.tournamentId = t2.tournamentId
}

fact creatorIsNotCollaborator{
    no disj t : Tournament| t.creator in t.collaborators
}
fact allBattlesHaveOneTournamentId{
    no disj t: Tournament|t.battles.tournamentId != t.tournamentId
}

--Battle
fact uniqueBattleId{
    no disj b1,b2 : Battle| b1.battleId = b2.battleId
}
//SICURI???
fact battleNameAreUnique{
	no disj b1,b2 : Battle  | b1.name = b2.name
}

fact noBattleNameWithoutBattle{
	all bn: BattleName | one b : Battle | b.name = bn
}
fact battleCreatorIsInTournament{
	all t:Tournament, b: t.battles | b.creator in t.collaborators
}

fact StudentOnlyInOneTeam{
    no disj s : Student, t1,t2 : Battle.teams |  s in t1.members && s in t2.members
}
fact noEvaluatorWithoutBattle{
  all e: Evaluator | one b : Battle | b.evaluator = e  
}

--User

fact usernameIsUnique{
	no disj u1,u2 :User | u1.username = u2.username 
}

fact emailIsUnique{
	no disj u1,u2 :User | u1.email = u2.email 
}


--Team
--probabilmente va in pred da qui non si puo fare
--fact TeamIsConstrained{
--	all b: Battle, t : b.teams | card[t] >= minTeamSize and card[t] <= maxTeamSize
--}
fact NoSharedPlayers {
  all b: Battle |
    no disj t1, t2: b.teams | t1.members & t2.members != none
}
fact uniqueTeamId{
    all b:Battle|
    no disj t1,t2 : b.teams| t1.teamId = t2.teamId
}
fact allTeamsHaveOneBattleId{
    no disj b: Battle|b.teams.battleId != b.battleId
}
-- Password
 fact noPasswordWithoutUser {
  all p: Password | one u: User | u. password = p
}

--Badges

fact uniqueBadgeId{
    no disj b1,b2 : Badge| b1.badgeId = b2.badgeId
}

fact noBadgeNameWithoutBadge{
	all bn: BadgeName | one b : Badge | b.name = bn
}





