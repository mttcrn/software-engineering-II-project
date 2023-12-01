sig Date {
	year: Int,
	month :Int,
	day: Int
}


abstract sig State{}
one sig Open extends State{}
one sig Close extends State{}
one sig OnGoing extends State{}

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
sig TournamentName{}
sig Tournament {
    tournamentId:  Int,
	subscriptionDeadline : Date,
	creator : Educator,
	name :  TournamentName,
	collaborators : set Educator,
	battles : some Battle,
	partecipants : some Student,
	state :  State,
	badges : set Badge
}	
	
abstract sig User{
	username :  Username,
	email :  Email,
	name : Name,
	surname :  Surname,
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
	size:Int
}


sig CodeKata{}
sig BattleName{}
sig Battle{
    battleId: Int,
    tournamentId:  Int,
	name :BattleName,
	creator : Educator,
	registrationDeadline : Date,
	submissionDeadline : Date,
	code : CodeKata,
	teams : set Team, 
	maxTeamSize :Int,
	minTeamSize:Int,
	state :  State,
    evaluator:  Evaluator
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
    tournament: Tournament
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
fact noTournamentScoreWithoutTournament{
	all ts: TournamentScore | one t:Tournament | t.name = ts.name
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
    all t: Tournament|t.battles.tournamentId = t.tournamentId
}
fact noSameStudentTwoTimes{
	all s1,s2:Tournament.partecipants| s1!=s2
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
	all t:Tournament, b: t.battles | (b.creator in t.collaborators) or ( b.creator=t.creator)
}

fact StudentOnlyInOneTeam{
    no disj s : Student, t1,t2 : Battle.teams |  s in t1.members && s in t2.members
}
fact noEvaluatorWithoutBattle{
	all e: Evaluator | one b : Battle | b.evaluator = e  
}
fact noCodekataWithoutBattle{
	all ck:CodeKata | one b:Battle | b.code=ck
}
fact minSizeIsLessThanMaxSize{
	no disj b:Battle | b.minTeamSize>b.maxTeamSize
}
fact subDeadlineMinorRegDeadline {
    all t: Tournament, b: t.battles |
         (b.registrationDeadline.year > t.subscriptionDeadline.year) or
        (b.registrationDeadline.year = t.subscriptionDeadline.year and
         (b.registrationDeadline.month > t.subscriptionDeadline.month or
          (b.registrationDeadline.month = t.subscriptionDeadline.month and
           b.registrationDeadline.day > t.subscriptionDeadline.day)))
}
fact subMissionMajorRegDeadline {
    all b:Battle|
         (b.registrationDeadline.year < b.submissionDeadline.year) or
        (b.registrationDeadline.year = b.submissionDeadline.year and
         (b.registrationDeadline.month < b.submissionDeadline.month or
          (b.registrationDeadline.month = b.submissionDeadline.month and
           b.registrationDeadline.day < b.submissionDeadline.day)))
}

--User

fact usernameIsUnique{
	no disj u1,u2 :User | u1.username = u2.username 
}

fact emailIsUnique{
	no disj u1,u2 :User | u1.email = u2.email 
}


--Username

fact noUsernameWithoutUser{
	all un: Username | one u : User | u.username=un
}


--Team


fact TeamIsConstrained{
	all b: Battle, t : b.teams | t.size >= b.minTeamSize and t.size <= b.maxTeamSize
}
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
fact noTeamWithoutStudents{
	all tm: Team | some s: Student| s in tm.members
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
	all bn: BadgeName | one b : Badge | b.title = bn
}
fact noBadgeWithoutTournament{
	all b:Badge |one t:Tournament| b.tournament=t
}





---------------------------------------------------
--Predicates
---------------------------------------------------

-- pred per stato torneo 3


pred world1{
	#Tournament=1
	#Student=2
	#Battle=3
	#Educator=1
}
run world1 for 5 





