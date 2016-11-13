sig RegisteredUser { position: Position }

sig Car {
    position:       Position,
    passengers:     Int,
    status:         one CarStatus
    }

sig ReservationTable {
    reserve: RegisteredUser -> lone Car
}

sig Ride {
   startPosition:   Position,
   endPosition:     Position,
   user:            one RegisteredUser,
   car:             one Car,
   status:          one RideStatus
}

abstract sig Position {}
sig CurrentPosition, SafeArea, PowerGridStation extends Position {}

/* ------------------ ENUMS ------------------ */

enum CarStatus {
        AVAILABLE,
        UNAVAILABLE,
        RESERVED,
        IN_USE
}

enum RideStatus {
        ACTIVE,
        ENDED
}

/* ------------------ FACTS ------------------ */
// If the car has passangers it means that it's in use
fact onlyInUseCarsCanHavePassengers {
    all c: Car | c.passengers > 0 implies c.status = IN_USE
}

// A user can be associated with just one acttive ride
fact onlyOneActiveRidePerUser {
    no u: RegisteredUser | some r1,r2: Ride | r1.status = ACTIVE and r2.status = ACTIVE
        and r1.user = u and r2.user = u and r1!=r2
}

// Rides should start or ends in PowerGridStations or SafeAreas and not in
// generic CurrentPosition
fact rideStartPoint{
    all r: Ride | all s: Position | s = r.startPosition implies
        s in PowerGridStation or s in SafeArea 
}
fact rideEndPoint{
    all r: Ride | all e: Position | e = r.endPosition implies e in PowerGridStation or e in SafeArea 
}

// A car is associated with a ride iff is in use
fact carInUseAreRelatedToActiveRides {
    all c: Car | all r:Ride | c.status = IN_USE implies (r.car = c and r.status = ACTIVE)
    all c: Car | all r:Ride | (r.car = c and r.status = ACTIVE) implies c.status = IN_USE
        /*and (r.status = ACTIVE and r.car = c) implies c.status = IN_USE*/
    /*all c: Car, r: Ride | r.status = ACTIVE and c.status = IN_USE implies (r.car = c)*/
    /*no c: Car | some r: Ride | c.status = IN_USE and c not in r.car*/
}

// A reserved car is associated to a ReservationTable
fact allReservedCarsAreInTheReservationTable {
    all c: Car | some u: RegisteredUser | c.status = RESERVED implies (c in u.( ReservationTable.reserve ))
}

// A car can be reserved only by one user
fact onlyOneUserReservesCar {
    no c: Car | some u1,u2: RegisteredUser | c in u1.(ReservationTable.reserve)
        and c in u2.(ReservationTable.reserve) and u1!=u2
}

// A reserved car has status 2
fact reservedCarStatus {
    all c: Car, u: RegisteredUser | c in u.(ReservationTable.reserve)
        implies c.status = RESERVED
}

// A car can be driven only by one user
fact onlyOneUserDriveCar {
    no r1, r2: Ride | r1.car = r2.car and r1!=r2
}

// Safe areas and power grid stations are only meant for cars
fact noSafeOrGridForUser {
    no u: RegisteredUser | u.position in SafeArea or u.position in PowerGridStation    
}

// Two cars can't have the same position
fact noCarsInTheSamePosition {
   no c1,c2: Car | c1.position = c2.position and c1!=c2 
}

// Two users can't have the same position
fact noUsersInTheSamePosition {
   no u1,u2: RegisteredUser | u1.position = u2.position and u1!=u2 
}

// A ride exists only if there is a user drving a car
fact noRideWithoutUserAndCar {
    /*no r: Ride | r.    */
}

// No more than four passengers in a car no less than 0
fact minMaxPassengersInCar {
    no c: Car | c.passengers > 4 or c.passengers < 0 
}

// If a car has passengers, then it needs to be in a ride
fact noUnattendedPassengers {
   /*no c:Car | no u:RegisteredUser | c.passengers > 0 and c not in u.(Ride.drive)*/
   no c:Car | some r: Ride | c.passengers > 0 and r.car!=c
    }


/* ------------------ ASSERTIONS ------------------ */
// A1
assert reservedStatusIfReallyReserved {
    no c: Car | some u: RegisteredUser |
        c in u.(ReservationTable.reserve) and c.status != RESERVED 
}
check reservedStatusIfReallyReserved for 10 but 1 ReservationTable

// A2
assert activeCarsAreInvolvedInAnActiveRide {
    all r: Ride | all c: Car |
        (r.car = c and r.status = ACTIVE) implies (c.status = IN_USE)
}
check activeCarsAreInvolvedInAnActiveRide for 10 but 1 ReservationTable

//A3
assert carsNotInUseDontHavePassengers {
    no c: Car | c.status != IN_USE and c.passengers > 0
}
check carsNotInUseDontHavePassengers for 10 but 1 ReservationTable

//A4
assert carsInUseCanHavePassengers {
    all c: Car | c.passengers > 0 implies ( c.status = IN_USE)
}
check carsInUseCanHavePassengers for 10 but 1 ReservationTable

//A5
assert carReservedAndAssociatedToRideMeansRideIsEnded {
    all c: Car, r: Ride | (r.car = c and c.status = RESERVED) implies r.status = ENDED
}
check carReservedAndAssociatedToRideMeansRideIsEnded


pred show() {}
run show for 5 but 1 ReservationTable
