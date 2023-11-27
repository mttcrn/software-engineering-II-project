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

abstract sig User{
	username : Username,
	email : Email,
	name : Name,
	surname : Surname,
	password : Password
} 

sig Student extends User{}
sig Educator extends User{}
sig Team{
	members : some Student
}


sig Problem{}
abstract sig State{}
one sig Open extends State{}
one sig Close extends State{}

sig BattleName{}
sig Battle{
	name :BattleName,
	creator : Educator,
	enrollDeadline : DateTime,
	submissionDeadline : DateTime,
	problem : Problem,
	teams : set Team,
	maxTeamSize :Int,
	minTeamSize:Int,
	state : one State
}
sig Badge {}
sig TournamentName{}
sig Tournament {
	enrollDeadline : DateTime,
	creator :Educator,
	name : TournamentName,
	educators : some Educator,
	battles : some Battle,
	partecipants : some Student,
	state : one State,
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
	all t : Tournament | t.creator in t.educators
}

--Battle

fact battleNameAreUnique{
	no disj b1,b2 : Battle  | b1.name = b2.name
}

fact noBattleNameWithoutBattle{
	all bn: BattleName | one b : Battle | b.name = bn
}
fact battleCreatorIsInTournament{
	all t:Tournament, b: t.battles | b.creator in t.educators
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















