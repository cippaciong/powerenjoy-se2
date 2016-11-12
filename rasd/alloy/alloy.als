sig RegisteredUser { position: Position }

sig Car {
    position:       Position,
    passengers:     Int,
    /*We need a hack for the status of the car. We have neither strings nor enums*/
    /*so we will map statuses to integers*/
    /*UNAVAILABLE:    0*/
    /*AVAILABLE:      1*/
    /*RESERVED:       2*/
    /*IN_USE:         3*/
    status:         one Int
    }

sig ReservationTable {
    reserve: RegisteredUser -> lone Car
}

sig Ride {
   startPosition:   Position,
   endPosition:     Position,
   user:            one RegisteredUser,
   car:             one Car,
   status:          one Int //0 inactive, 1 active
}

abstract sig Position {}
sig CurrentPosition, SafeArea, PowerGridStation extends Position {}

/* ------------------ FACTS ------------------ */
// The status of the car can be either 0, 1, 2 or 3
fact onlyFourStatusesForCars {
    all c: Car | c.status >= 0 and c.status < 4
}
// The status of the ride can be either 0 or 1
fact onlyTwoStatusForRide {
    all r: Ride | r.status = 0 or r.status = 1
}

// If the car has passangers it means that it's in use (status 3)
fact onlyInUseCarsCanHavePassengers {
    all c: Car | c.passengers > 0 implies c.status = 3
}

// A user can be associated with just one acttive ride
fact onlyOneActiveRidePerUser {
    no u: RegisteredUser | some r1,r2: Ride | r1.status = 1 and r2.status = 1
        and r1.user = u and r2.user = u and r1!=r2
}

// Rides should start or ends in PowerGridStations or SafeAreas and not in
// generic CurrentPosition
fact rideStartPoint{
    all r: Ride | all s: Position | s = r.startPosition implies s in PowerGridStation or s in SafeArea 
        /*e = r.startPosition implies e in PowerGridStation or e in SafeArea*/
}
fact rideEndPoint{
    all r: Ride | all e: Position | e = r.endPosition implies e in PowerGridStation or e in SafeArea 
}

// A car is associated with a ride iff is in use
fact carInUseAreRelatedToActiveRides {
    all c: Car, r: Ride | r.status = 1 and c.status = 3 implies (r.car = c)
}

// A car can be reserved only by one user
fact onlyOneUserReservesCar {
    no c: Car | some u1,u2: RegisteredUser | c in u1.(ReservationTable.reserve)
        and c in u2.(ReservationTable.reserve) and u1!=u2
}

// A reserved car has status 2
fact reservedCarStatus {
    all c: Car, u: RegisteredUser | c in u.(ReservationTable.reserve)
        implies c.status = 2    
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


pred show() {}
run show for 5 but 1 ReservationTable
