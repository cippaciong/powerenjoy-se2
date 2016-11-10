sig RegisteredUser {}

sig Car{}

sig Reservation {reserve: RegisteredUser -> Car}

pred show(r: Reservation) {
   #r.reserve 
    }
run show for 3 but 1 Reservation
