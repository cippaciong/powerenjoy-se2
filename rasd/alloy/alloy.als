sig RegisteredUser {}

sig Car{
    currentOwner:   lone RegisteredUser    
}

sig Reservation {
    userReserving:  lone RegisteredUser,
    carToReserve:   lone Car
}

fact userReserveOneCarAtATime {
    no u: RegisteredUser | some c1,c2: Car | c1!=c2 and u in c1.currentOwner and u in c2.currentOwner
}
pred show() {}
run show for 3 but 1 Reservation
