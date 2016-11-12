sig RegisteredUser { position: Position }

sig Car {
    position:       Position,
    passengers:     Int
    }

sig ReservationTable {
    reserve: RegisteredUser -> lone Car
}

sig Ride {
   startPosition:   Position,
   endPosition:     Position,
   user:            RegisteredUser,
   car:             Car
}

fact noCurrentPosition {
    no r: Ride | r.startPosition in CurrentPosition or r.endPosition in CurrentPosition
}
abstract sig Position {}
sig CurrentPosition, SafeArea, PowerGridStation extends Position {}

// A car can be reserved only by one user
fact onlyOneUserReservesCar {
    no c: Car | some u1,u2: RegisteredUser | c in u1.(ReservationTable.reserve)
        and c in u2.(ReservationTable.reserve) and u1!=u2
}

// A car can be drove only by one user
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
run show for 3 but 1 ReservationTable
