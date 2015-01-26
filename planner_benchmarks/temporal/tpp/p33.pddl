(define (problem pfile33)
(:domain TPP-MetricTime)
(:objects
	market1 market2 market3 market4 market5 market6 market7 market8 market9 - market
	depot1 depot2 depot3 depot4 - depot
	truck1 truck2 truck3 truck4 truck5 truck6 truck7 truck8 truck9 - truck
	goods1 goods2 goods3 goods4 goods5 goods6 goods7 goods8 goods9 goods10 goods11 goods12 goods13 goods14 goods15 goods16 goods17 goods18 - goods)

(:init
	(= (price goods1 market1) 49)
	(= (ready-to-load goods1 market1) 0)
	(= (on-sale goods1 market1) 17)
	(= (ready-to-load goods1 market2) 0)
	(= (on-sale goods1 market2) 0)
	(= (ready-to-load goods1 market3) 0)
	(= (on-sale goods1 market3) 0)
	(= (price goods1 market4) 15)
	(= (ready-to-load goods1 market4) 0)
	(= (on-sale goods1 market4) 16)
	(= (ready-to-load goods1 market5) 0)
	(= (on-sale goods1 market5) 0)
	(= (ready-to-load goods1 market6) 0)
	(= (on-sale goods1 market6) 0)
	(= (ready-to-load goods1 market7) 0)
	(= (on-sale goods1 market7) 0)
	(= (price goods1 market8) 24)
	(= (ready-to-load goods1 market8) 0)
	(= (on-sale goods1 market8) 4)
	(= (price goods1 market9) 4)
	(= (ready-to-load goods1 market9) 0)
	(= (on-sale goods1 market9) 16)
	(= (ready-to-load goods2 market1) 0)
	(= (on-sale goods2 market1) 0)
	(= (ready-to-load goods2 market2) 0)
	(= (on-sale goods2 market2) 0)
	(= (price goods2 market3) 18)
	(= (ready-to-load goods2 market3) 0)
	(= (on-sale goods2 market3) 17)
	(= (price goods2 market4) 17)
	(= (ready-to-load goods2 market4) 0)
	(= (on-sale goods2 market4) 3)
	(= (ready-to-load goods2 market5) 0)
	(= (on-sale goods2 market5) 0)
	(= (ready-to-load goods2 market6) 0)
	(= (on-sale goods2 market6) 0)
	(= (price goods2 market7) 9)
	(= (ready-to-load goods2 market7) 0)
	(= (on-sale goods2 market7) 20)
	(= (price goods2 market8) 15)
	(= (ready-to-load goods2 market8) 0)
	(= (on-sale goods2 market8) 18)
	(= (price goods2 market9) 11)
	(= (ready-to-load goods2 market9) 0)
	(= (on-sale goods2 market9) 15)
	(= (ready-to-load goods3 market1) 0)
	(= (on-sale goods3 market1) 0)
	(= (price goods3 market2) 12)
	(= (ready-to-load goods3 market2) 0)
	(= (on-sale goods3 market2) 5)
	(= (ready-to-load goods3 market3) 0)
	(= (on-sale goods3 market3) 0)
	(= (price goods3 market4) 47)
	(= (ready-to-load goods3 market4) 0)
	(= (on-sale goods3 market4) 3)
	(= (price goods3 market5) 24)
	(= (ready-to-load goods3 market5) 0)
	(= (on-sale goods3 market5) 11)
	(= (price goods3 market6) 32)
	(= (ready-to-load goods3 market6) 0)
	(= (on-sale goods3 market6) 16)
	(= (ready-to-load goods3 market7) 0)
	(= (on-sale goods3 market7) 0)
	(= (price goods3 market8) 36)
	(= (ready-to-load goods3 market8) 0)
	(= (on-sale goods3 market8) 1)
	(= (price goods3 market9) 36)
	(= (ready-to-load goods3 market9) 0)
	(= (on-sale goods3 market9) 8)
	(= (ready-to-load goods4 market1) 0)
	(= (on-sale goods4 market1) 0)
	(= (price goods4 market2) 8)
	(= (ready-to-load goods4 market2) 0)
	(= (on-sale goods4 market2) 5)
	(= (ready-to-load goods4 market3) 0)
	(= (on-sale goods4 market3) 0)
	(= (price goods4 market4) 1)
	(= (ready-to-load goods4 market4) 0)
	(= (on-sale goods4 market4) 2)
	(= (price goods4 market5) 13)
	(= (ready-to-load goods4 market5) 0)
	(= (on-sale goods4 market5) 12)
	(= (ready-to-load goods4 market6) 0)
	(= (on-sale goods4 market6) 0)
	(= (price goods4 market7) 3)
	(= (ready-to-load goods4 market7) 0)
	(= (on-sale goods4 market7) 16)
	(= (ready-to-load goods4 market8) 0)
	(= (on-sale goods4 market8) 0)
	(= (price goods4 market9) 47)
	(= (ready-to-load goods4 market9) 0)
	(= (on-sale goods4 market9) 11)
	(= (ready-to-load goods5 market1) 0)
	(= (on-sale goods5 market1) 0)
	(= (ready-to-load goods5 market2) 0)
	(= (on-sale goods5 market2) 0)
	(= (price goods5 market3) 8)
	(= (ready-to-load goods5 market3) 0)
	(= (on-sale goods5 market3) 7)
	(= (price goods5 market4) 10)
	(= (ready-to-load goods5 market4) 0)
	(= (on-sale goods5 market4) 18)
	(= (price goods5 market5) 27)
	(= (ready-to-load goods5 market5) 0)
	(= (on-sale goods5 market5) 15)
	(= (price goods5 market6) 12)
	(= (ready-to-load goods5 market6) 0)
	(= (on-sale goods5 market6) 4)
	(= (price goods5 market7) 3)
	(= (ready-to-load goods5 market7) 0)
	(= (on-sale goods5 market7) 11)
	(= (price goods5 market8) 6)
	(= (ready-to-load goods5 market8) 0)
	(= (on-sale goods5 market8) 4)
	(= (price goods5 market9) 18)
	(= (ready-to-load goods5 market9) 0)
	(= (on-sale goods5 market9) 15)
	(= (ready-to-load goods6 market1) 0)
	(= (on-sale goods6 market1) 0)
	(= (price goods6 market2) 30)
	(= (ready-to-load goods6 market2) 0)
	(= (on-sale goods6 market2) 4)
	(= (price goods6 market3) 30)
	(= (ready-to-load goods6 market3) 0)
	(= (on-sale goods6 market3) 13)
	(= (price goods6 market4) 5)
	(= (ready-to-load goods6 market4) 0)
	(= (on-sale goods6 market4) 5)
	(= (ready-to-load goods6 market5) 0)
	(= (on-sale goods6 market5) 0)
	(= (ready-to-load goods6 market6) 0)
	(= (on-sale goods6 market6) 0)
	(= (ready-to-load goods6 market7) 0)
	(= (on-sale goods6 market7) 0)
	(= (ready-to-load goods6 market8) 0)
	(= (on-sale goods6 market8) 0)
	(= (price goods6 market9) 39)
	(= (ready-to-load goods6 market9) 0)
	(= (on-sale goods6 market9) 2)
	(= (price goods7 market1) 24)
	(= (ready-to-load goods7 market1) 0)
	(= (on-sale goods7 market1) 10)
	(= (ready-to-load goods7 market2) 0)
	(= (on-sale goods7 market2) 0)
	(= (price goods7 market3) 33)
	(= (ready-to-load goods7 market3) 0)
	(= (on-sale goods7 market3) 13)
	(= (price goods7 market4) 27)
	(= (ready-to-load goods7 market4) 0)
	(= (on-sale goods7 market4) 17)
	(= (ready-to-load goods7 market5) 0)
	(= (on-sale goods7 market5) 0)
	(= (ready-to-load goods7 market6) 0)
	(= (on-sale goods7 market6) 0)
	(= (ready-to-load goods7 market7) 0)
	(= (on-sale goods7 market7) 0)
	(= (ready-to-load goods7 market8) 0)
	(= (on-sale goods7 market8) 0)
	(= (price goods7 market9) 35)
	(= (ready-to-load goods7 market9) 0)
	(= (on-sale goods7 market9) 5)
	(= (ready-to-load goods8 market1) 0)
	(= (on-sale goods8 market1) 0)
	(= (price goods8 market2) 8)
	(= (ready-to-load goods8 market2) 0)
	(= (on-sale goods8 market2) 20)
	(= (ready-to-load goods8 market3) 0)
	(= (on-sale goods8 market3) 0)
	(= (ready-to-load goods8 market4) 0)
	(= (on-sale goods8 market4) 0)
	(= (price goods8 market5) 34)
	(= (ready-to-load goods8 market5) 0)
	(= (on-sale goods8 market5) 6)
	(= (ready-to-load goods8 market6) 0)
	(= (on-sale goods8 market6) 0)
	(= (ready-to-load goods8 market7) 0)
	(= (on-sale goods8 market7) 0)
	(= (price goods8 market8) 36)
	(= (ready-to-load goods8 market8) 0)
	(= (on-sale goods8 market8) 1)
	(= (price goods8 market9) 9)
	(= (ready-to-load goods8 market9) 0)
	(= (on-sale goods8 market9) 11)
	(= (ready-to-load goods9 market1) 0)
	(= (on-sale goods9 market1) 0)
	(= (price goods9 market2) 7)
	(= (ready-to-load goods9 market2) 0)
	(= (on-sale goods9 market2) 1)
	(= (price goods9 market3) 33)
	(= (ready-to-load goods9 market3) 0)
	(= (on-sale goods9 market3) 10)
	(= (price goods9 market4) 38)
	(= (ready-to-load goods9 market4) 0)
	(= (on-sale goods9 market4) 10)
	(= (ready-to-load goods9 market5) 0)
	(= (on-sale goods9 market5) 0)
	(= (ready-to-load goods9 market6) 0)
	(= (on-sale goods9 market6) 0)
	(= (ready-to-load goods9 market7) 0)
	(= (on-sale goods9 market7) 0)
	(= (price goods9 market8) 31)
	(= (ready-to-load goods9 market8) 0)
	(= (on-sale goods9 market8) 6)
	(= (price goods9 market9) 9)
	(= (ready-to-load goods9 market9) 0)
	(= (on-sale goods9 market9) 16)
	(= (ready-to-load goods10 market1) 0)
	(= (on-sale goods10 market1) 0)
	(= (price goods10 market2) 16)
	(= (ready-to-load goods10 market2) 0)
	(= (on-sale goods10 market2) 7)
	(= (ready-to-load goods10 market3) 0)
	(= (on-sale goods10 market3) 0)
	(= (price goods10 market4) 28)
	(= (ready-to-load goods10 market4) 0)
	(= (on-sale goods10 market4) 3)
	(= (price goods10 market5) 30)
	(= (ready-to-load goods10 market5) 0)
	(= (on-sale goods10 market5) 15)
	(= (price goods10 market6) 44)
	(= (ready-to-load goods10 market6) 0)
	(= (on-sale goods10 market6) 9)
	(= (ready-to-load goods10 market7) 0)
	(= (on-sale goods10 market7) 0)
	(= (price goods10 market8) 32)
	(= (ready-to-load goods10 market8) 0)
	(= (on-sale goods10 market8) 16)
	(= (price goods10 market9) 31)
	(= (ready-to-load goods10 market9) 0)
	(= (on-sale goods10 market9) 7)
	(= (ready-to-load goods11 market1) 0)
	(= (on-sale goods11 market1) 0)
	(= (price goods11 market2) 21)
	(= (ready-to-load goods11 market2) 0)
	(= (on-sale goods11 market2) 10)
	(= (price goods11 market3) 3)
	(= (ready-to-load goods11 market3) 0)
	(= (on-sale goods11 market3) 8)
	(= (ready-to-load goods11 market4) 0)
	(= (on-sale goods11 market4) 0)
	(= (price goods11 market5) 10)
	(= (ready-to-load goods11 market5) 0)
	(= (on-sale goods11 market5) 11)
	(= (price goods11 market6) 27)
	(= (ready-to-load goods11 market6) 0)
	(= (on-sale goods11 market6) 9)
	(= (price goods11 market7) 9)
	(= (ready-to-load goods11 market7) 0)
	(= (on-sale goods11 market7) 13)
	(= (price goods11 market8) 4)
	(= (ready-to-load goods11 market8) 0)
	(= (on-sale goods11 market8) 4)
	(= (price goods11 market9) 22)
	(= (ready-to-load goods11 market9) 0)
	(= (on-sale goods11 market9) 3)
	(= (ready-to-load goods12 market1) 0)
	(= (on-sale goods12 market1) 0)
	(= (price goods12 market2) 3)
	(= (ready-to-load goods12 market2) 0)
	(= (on-sale goods12 market2) 17)
	(= (ready-to-load goods12 market3) 0)
	(= (on-sale goods12 market3) 0)
	(= (ready-to-load goods12 market4) 0)
	(= (on-sale goods12 market4) 0)
	(= (price goods12 market5) 5)
	(= (ready-to-load goods12 market5) 0)
	(= (on-sale goods12 market5) 19)
	(= (ready-to-load goods12 market6) 0)
	(= (on-sale goods12 market6) 0)
	(= (ready-to-load goods12 market7) 0)
	(= (on-sale goods12 market7) 0)
	(= (ready-to-load goods12 market8) 0)
	(= (on-sale goods12 market8) 0)
	(= (price goods12 market9) 27)
	(= (ready-to-load goods12 market9) 0)
	(= (on-sale goods12 market9) 7)
	(= (ready-to-load goods13 market1) 0)
	(= (on-sale goods13 market1) 0)
	(= (ready-to-load goods13 market2) 0)
	(= (on-sale goods13 market2) 0)
	(= (price goods13 market3) 46)
	(= (ready-to-load goods13 market3) 0)
	(= (on-sale goods13 market3) 20)
	(= (ready-to-load goods13 market4) 0)
	(= (on-sale goods13 market4) 0)
	(= (ready-to-load goods13 market5) 0)
	(= (on-sale goods13 market5) 0)
	(= (price goods13 market6) 25)
	(= (ready-to-load goods13 market6) 0)
	(= (on-sale goods13 market6) 2)
	(= (ready-to-load goods13 market7) 0)
	(= (on-sale goods13 market7) 0)
	(= (ready-to-load goods13 market8) 0)
	(= (on-sale goods13 market8) 0)
	(= (price goods13 market9) 10)
	(= (ready-to-load goods13 market9) 0)
	(= (on-sale goods13 market9) 4)
	(= (ready-to-load goods14 market1) 0)
	(= (on-sale goods14 market1) 0)
	(= (ready-to-load goods14 market2) 0)
	(= (on-sale goods14 market2) 0)
	(= (ready-to-load goods14 market3) 0)
	(= (on-sale goods14 market3) 0)
	(= (price goods14 market4) 50)
	(= (ready-to-load goods14 market4) 0)
	(= (on-sale goods14 market4) 5)
	(= (price goods14 market5) 20)
	(= (ready-to-load goods14 market5) 0)
	(= (on-sale goods14 market5) 5)
	(= (ready-to-load goods14 market6) 0)
	(= (on-sale goods14 market6) 0)
	(= (price goods14 market7) 37)
	(= (ready-to-load goods14 market7) 0)
	(= (on-sale goods14 market7) 19)
	(= (ready-to-load goods14 market8) 0)
	(= (on-sale goods14 market8) 0)
	(= (price goods14 market9) 1)
	(= (ready-to-load goods14 market9) 0)
	(= (on-sale goods14 market9) 15)
	(= (ready-to-load goods15 market1) 0)
	(= (on-sale goods15 market1) 0)
	(= (price goods15 market2) 24)
	(= (ready-to-load goods15 market2) 0)
	(= (on-sale goods15 market2) 20)
	(= (ready-to-load goods15 market3) 0)
	(= (on-sale goods15 market3) 0)
	(= (price goods15 market4) 37)
	(= (ready-to-load goods15 market4) 0)
	(= (on-sale goods15 market4) 13)
	(= (ready-to-load goods15 market5) 0)
	(= (on-sale goods15 market5) 0)
	(= (ready-to-load goods15 market6) 0)
	(= (on-sale goods15 market6) 0)
	(= (ready-to-load goods15 market7) 0)
	(= (on-sale goods15 market7) 0)
	(= (ready-to-load goods15 market8) 0)
	(= (on-sale goods15 market8) 0)
	(= (price goods15 market9) 9)
	(= (ready-to-load goods15 market9) 0)
	(= (on-sale goods15 market9) 3)
	(= (price goods16 market1) 6)
	(= (ready-to-load goods16 market1) 0)
	(= (on-sale goods16 market1) 16)
	(= (price goods16 market2) 13)
	(= (ready-to-load goods16 market2) 0)
	(= (on-sale goods16 market2) 17)
	(= (ready-to-load goods16 market3) 0)
	(= (on-sale goods16 market3) 0)
	(= (ready-to-load goods16 market4) 0)
	(= (on-sale goods16 market4) 0)
	(= (ready-to-load goods16 market5) 0)
	(= (on-sale goods16 market5) 0)
	(= (price goods16 market6) 13)
	(= (ready-to-load goods16 market6) 0)
	(= (on-sale goods16 market6) 15)
	(= (ready-to-load goods16 market7) 0)
	(= (on-sale goods16 market7) 0)
	(= (ready-to-load goods16 market8) 0)
	(= (on-sale goods16 market8) 0)
	(= (price goods16 market9) 9)
	(= (ready-to-load goods16 market9) 0)
	(= (on-sale goods16 market9) 16)
	(= (ready-to-load goods17 market1) 0)
	(= (on-sale goods17 market1) 0)
	(= (ready-to-load goods17 market2) 0)
	(= (on-sale goods17 market2) 0)
	(= (ready-to-load goods17 market3) 0)
	(= (on-sale goods17 market3) 0)
	(= (price goods17 market4) 24)
	(= (ready-to-load goods17 market4) 0)
	(= (on-sale goods17 market4) 14)
	(= (price goods17 market5) 38)
	(= (ready-to-load goods17 market5) 0)
	(= (on-sale goods17 market5) 3)
	(= (ready-to-load goods17 market6) 0)
	(= (on-sale goods17 market6) 0)
	(= (ready-to-load goods17 market7) 0)
	(= (on-sale goods17 market7) 0)
	(= (price goods17 market8) 32)
	(= (ready-to-load goods17 market8) 0)
	(= (on-sale goods17 market8) 15)
	(= (price goods17 market9) 39)
	(= (ready-to-load goods17 market9) 0)
	(= (on-sale goods17 market9) 11)
	(= (price goods18 market1) 2)
	(= (ready-to-load goods18 market1) 0)
	(= (on-sale goods18 market1) 19)
	(= (price goods18 market2) 28)
	(= (ready-to-load goods18 market2) 0)
	(= (on-sale goods18 market2) 7)
	(= (price goods18 market3) 40)
	(= (ready-to-load goods18 market3) 0)
	(= (on-sale goods18 market3) 1)
	(= (ready-to-load goods18 market4) 0)
	(= (on-sale goods18 market4) 0)
	(= (ready-to-load goods18 market5) 0)
	(= (on-sale goods18 market5) 0)
	(= (ready-to-load goods18 market6) 0)
	(= (on-sale goods18 market6) 0)
	(= (ready-to-load goods18 market7) 0)
	(= (on-sale goods18 market7) 0)
	(= (ready-to-load goods18 market8) 0)
	(= (on-sale goods18 market8) 0)
	(= (price goods18 market9) 44)
	(= (ready-to-load goods18 market9) 0)
	(= (on-sale goods18 market9) 16)
	(connected market1 market3)
	(connected market3 market1)
	(= (drive-cost market1 market3) 962.00)
	(= (drive-cost market3 market1) 962.00)
	(= (drive-time market1 market3) 2886.00)
	(= (drive-time market3 market1) 2886.00)
	(connected market1 market4)
	(connected market4 market1)
	(= (drive-cost market1 market4) 628.00)
	(= (drive-cost market4 market1) 628.00)
	(= (drive-time market1 market4) 1884.00)
	(= (drive-time market4 market1) 1884.00)
	(connected market1 market5)
	(connected market5 market1)
	(= (drive-cost market1 market5) 173.00)
	(= (drive-cost market5 market1) 173.00)
	(= (drive-time market1 market5) 519.00)
	(= (drive-time market5 market1) 519.00)
	(connected market1 market6)
	(connected market6 market1)
	(= (drive-cost market1 market6) 892.00)
	(= (drive-cost market6 market1) 892.00)
	(= (drive-time market1 market6) 2676.00)
	(= (drive-time market6 market1) 2676.00)
	(connected market1 market7)
	(connected market7 market1)
	(= (drive-cost market1 market7) 124.00)
	(= (drive-cost market7 market1) 124.00)
	(= (drive-time market1 market7) 372.00)
	(= (drive-time market7 market1) 372.00)
	(connected market1 market9)
	(connected market9 market1)
	(= (drive-cost market1 market9) 713.00)
	(= (drive-cost market9 market1) 713.00)
	(= (drive-time market1 market9) 2139.00)
	(= (drive-time market9 market1) 2139.00)
	(connected market2 market3)
	(connected market3 market2)
	(= (drive-cost market2 market3) 173.00)
	(= (drive-cost market3 market2) 173.00)
	(= (drive-time market2 market3) 519.00)
	(= (drive-time market3 market2) 519.00)
	(connected market2 market4)
	(connected market4 market2)
	(= (drive-cost market2 market4) 228.00)
	(= (drive-cost market4 market2) 228.00)
	(= (drive-time market2 market4) 684.00)
	(= (drive-time market4 market2) 684.00)
	(connected market2 market5)
	(connected market5 market2)
	(= (drive-cost market2 market5) 624.00)
	(= (drive-cost market5 market2) 624.00)
	(= (drive-time market2 market5) 1872.00)
	(= (drive-time market5 market2) 1872.00)
	(connected market2 market6)
	(connected market6 market2)
	(= (drive-cost market2 market6) 941.00)
	(= (drive-cost market6 market2) 941.00)
	(= (drive-time market2 market6) 2823.00)
	(= (drive-time market6 market2) 2823.00)
	(connected market2 market7)
	(connected market7 market2)
	(= (drive-cost market2 market7) 674.00)
	(= (drive-cost market7 market2) 674.00)
	(= (drive-time market2 market7) 2022.00)
	(= (drive-time market7 market2) 2022.00)
	(connected market2 market8)
	(connected market8 market2)
	(= (drive-cost market2 market8) 87.00)
	(= (drive-cost market8 market2) 87.00)
	(= (drive-time market2 market8) 261.00)
	(= (drive-time market8 market2) 261.00)
	(connected market2 market9)
	(connected market9 market2)
	(= (drive-cost market2 market9) 235.00)
	(= (drive-cost market9 market2) 235.00)
	(= (drive-time market2 market9) 705.00)
	(= (drive-time market9 market2) 705.00)
	(connected market3 market4)
	(connected market4 market3)
	(= (drive-cost market3 market4) 803.00)
	(= (drive-cost market4 market3) 803.00)
	(= (drive-time market3 market4) 2409.00)
	(= (drive-time market4 market3) 2409.00)
	(connected market3 market5)
	(connected market5 market3)
	(= (drive-cost market3 market5) 162.00)
	(= (drive-cost market5 market3) 162.00)
	(= (drive-time market3 market5) 486.00)
	(= (drive-time market5 market3) 486.00)
	(connected market3 market7)
	(connected market7 market3)
	(= (drive-cost market3 market7) 903.00)
	(= (drive-cost market7 market3) 903.00)
	(= (drive-time market3 market7) 2709.00)
	(= (drive-time market7 market3) 2709.00)
	(connected market3 market8)
	(connected market8 market3)
	(= (drive-cost market3 market8) 218.00)
	(= (drive-cost market8 market3) 218.00)
	(= (drive-time market3 market8) 654.00)
	(= (drive-time market8 market3) 654.00)
	(connected market3 market9)
	(connected market9 market3)
	(= (drive-cost market3 market9) 225.00)
	(= (drive-cost market9 market3) 225.00)
	(= (drive-time market3 market9) 675.00)
	(= (drive-time market9 market3) 675.00)
	(connected market4 market5)
	(connected market5 market4)
	(= (drive-cost market4 market5) 776.00)
	(= (drive-cost market5 market4) 776.00)
	(= (drive-time market4 market5) 2328.00)
	(= (drive-time market5 market4) 2328.00)
	(connected market4 market6)
	(connected market6 market4)
	(= (drive-cost market4 market6) 832.00)
	(= (drive-cost market6 market4) 832.00)
	(= (drive-time market4 market6) 2496.00)
	(= (drive-time market6 market4) 2496.00)
	(connected market4 market7)
	(connected market7 market4)
	(= (drive-cost market4 market7) 810.00)
	(= (drive-cost market7 market4) 810.00)
	(= (drive-time market4 market7) 2430.00)
	(= (drive-time market7 market4) 2430.00)
	(connected market4 market8)
	(connected market8 market4)
	(= (drive-cost market4 market8) 932.00)
	(= (drive-cost market8 market4) 932.00)
	(= (drive-time market4 market8) 2796.00)
	(= (drive-time market8 market4) 2796.00)
	(connected market5 market6)
	(connected market6 market5)
	(= (drive-cost market5 market6) 51.00)
	(= (drive-cost market6 market5) 51.00)
	(= (drive-time market5 market6) 153.00)
	(= (drive-time market6 market5) 153.00)
	(connected market5 market7)
	(connected market7 market5)
	(= (drive-cost market5 market7) 284.00)
	(= (drive-cost market7 market5) 284.00)
	(= (drive-time market5 market7) 852.00)
	(= (drive-time market7 market5) 852.00)
	(connected market5 market8)
	(connected market8 market5)
	(= (drive-cost market5 market8) 216.00)
	(= (drive-cost market8 market5) 216.00)
	(= (drive-time market5 market8) 648.00)
	(= (drive-time market8 market5) 648.00)
	(connected market5 market9)
	(connected market9 market5)
	(= (drive-cost market5 market9) 83.00)
	(= (drive-cost market9 market5) 83.00)
	(= (drive-time market5 market9) 249.00)
	(= (drive-time market9 market5) 249.00)
	(connected market6 market7)
	(connected market7 market6)
	(= (drive-cost market6 market7) 881.00)
	(= (drive-cost market7 market6) 881.00)
	(= (drive-time market6 market7) 2643.00)
	(= (drive-time market7 market6) 2643.00)
	(connected market6 market8)
	(connected market8 market6)
	(= (drive-cost market6 market8) 64.00)
	(= (drive-cost market8 market6) 64.00)
	(= (drive-time market6 market8) 192.00)
	(= (drive-time market8 market6) 192.00)
	(connected market6 market9)
	(connected market9 market6)
	(= (drive-cost market6 market9) 109.00)
	(= (drive-cost market9 market6) 109.00)
	(= (drive-time market6 market9) 327.00)
	(= (drive-time market9 market6) 327.00)
	(connected market7 market8)
	(connected market8 market7)
	(= (drive-cost market7 market8) 754.00)
	(= (drive-cost market8 market7) 754.00)
	(= (drive-time market7 market8) 2262.00)
	(= (drive-time market8 market7) 2262.00)
	(connected market7 market9)
	(connected market9 market7)
	(= (drive-cost market7 market9) 102.00)
	(= (drive-cost market9 market7) 102.00)
	(= (drive-time market7 market9) 306.00)
	(= (drive-time market9 market7) 306.00)
	(connected market8 market9)
	(connected market9 market8)
	(= (drive-cost market8 market9) 70.00)
	(= (drive-cost market9 market8) 70.00)
	(= (drive-time market8 market9) 210.00)
	(= (drive-time market9 market8) 210.00)
	(connected depot1 market1)
	(connected market1 depot1)
	(= (drive-cost market1 depot1) 734.00)
	(= (drive-cost depot1 market1) 734.00)
	(= (drive-time market1 depot1) 2202.00)
	(= (drive-time depot1 market1) 2202.00)
	(connected depot2 market8)
	(connected market8 depot2)
	(= (drive-cost market8 depot2) 964.00)
	(= (drive-cost depot2 market8) 964.00)
	(= (drive-time market8 depot2) 2892.00)
	(= (drive-time depot2 market8) 2892.00)
	(connected depot3 market9)
	(connected market9 depot3)
	(= (drive-cost market9 depot3) 594.00)
	(= (drive-cost depot3 market9) 594.00)
	(= (drive-time market9 depot3) 1782.00)
	(= (drive-time depot3 market9) 1782.00)
	(connected depot4 market9)
	(connected market9 depot4)
	(= (drive-cost market9 depot4) 538.00)
	(= (drive-cost depot4 market9) 538.00)
	(= (drive-time market9 depot4) 1614.00)
	(= (drive-time depot4 market9) 1614.00)
	(= (loaded goods1 truck1) 0)
	(= (loaded goods2 truck1) 0)
	(= (loaded goods3 truck1) 0)
	(= (loaded goods4 truck1) 0)
	(= (loaded goods5 truck1) 0)
	(= (loaded goods6 truck1) 0)
	(= (loaded goods7 truck1) 0)
	(= (loaded goods8 truck1) 0)
	(= (loaded goods9 truck1) 0)
	(= (loaded goods10 truck1) 0)
	(= (loaded goods11 truck1) 0)
	(= (loaded goods12 truck1) 0)
	(= (loaded goods13 truck1) 0)
	(= (loaded goods14 truck1) 0)
	(= (loaded goods15 truck1) 0)
	(= (loaded goods16 truck1) 0)
	(= (loaded goods17 truck1) 0)
	(= (loaded goods18 truck1) 0)
	(at truck1 depot4)
	(= (loaded goods1 truck2) 0)
	(= (loaded goods2 truck2) 0)
	(= (loaded goods3 truck2) 0)
	(= (loaded goods4 truck2) 0)
	(= (loaded goods5 truck2) 0)
	(= (loaded goods6 truck2) 0)
	(= (loaded goods7 truck2) 0)
	(= (loaded goods8 truck2) 0)
	(= (loaded goods9 truck2) 0)
	(= (loaded goods10 truck2) 0)
	(= (loaded goods11 truck2) 0)
	(= (loaded goods12 truck2) 0)
	(= (loaded goods13 truck2) 0)
	(= (loaded goods14 truck2) 0)
	(= (loaded goods15 truck2) 0)
	(= (loaded goods16 truck2) 0)
	(= (loaded goods17 truck2) 0)
	(= (loaded goods18 truck2) 0)
	(at truck2 depot4)
	(= (loaded goods1 truck3) 0)
	(= (loaded goods2 truck3) 0)
	(= (loaded goods3 truck3) 0)
	(= (loaded goods4 truck3) 0)
	(= (loaded goods5 truck3) 0)
	(= (loaded goods6 truck3) 0)
	(= (loaded goods7 truck3) 0)
	(= (loaded goods8 truck3) 0)
	(= (loaded goods9 truck3) 0)
	(= (loaded goods10 truck3) 0)
	(= (loaded goods11 truck3) 0)
	(= (loaded goods12 truck3) 0)
	(= (loaded goods13 truck3) 0)
	(= (loaded goods14 truck3) 0)
	(= (loaded goods15 truck3) 0)
	(= (loaded goods16 truck3) 0)
	(= (loaded goods17 truck3) 0)
	(= (loaded goods18 truck3) 0)
	(at truck3 depot2)
	(= (loaded goods1 truck4) 0)
	(= (loaded goods2 truck4) 0)
	(= (loaded goods3 truck4) 0)
	(= (loaded goods4 truck4) 0)
	(= (loaded goods5 truck4) 0)
	(= (loaded goods6 truck4) 0)
	(= (loaded goods7 truck4) 0)
	(= (loaded goods8 truck4) 0)
	(= (loaded goods9 truck4) 0)
	(= (loaded goods10 truck4) 0)
	(= (loaded goods11 truck4) 0)
	(= (loaded goods12 truck4) 0)
	(= (loaded goods13 truck4) 0)
	(= (loaded goods14 truck4) 0)
	(= (loaded goods15 truck4) 0)
	(= (loaded goods16 truck4) 0)
	(= (loaded goods17 truck4) 0)
	(= (loaded goods18 truck4) 0)
	(at truck4 depot4)
	(= (loaded goods1 truck5) 0)
	(= (loaded goods2 truck5) 0)
	(= (loaded goods3 truck5) 0)
	(= (loaded goods4 truck5) 0)
	(= (loaded goods5 truck5) 0)
	(= (loaded goods6 truck5) 0)
	(= (loaded goods7 truck5) 0)
	(= (loaded goods8 truck5) 0)
	(= (loaded goods9 truck5) 0)
	(= (loaded goods10 truck5) 0)
	(= (loaded goods11 truck5) 0)
	(= (loaded goods12 truck5) 0)
	(= (loaded goods13 truck5) 0)
	(= (loaded goods14 truck5) 0)
	(= (loaded goods15 truck5) 0)
	(= (loaded goods16 truck5) 0)
	(= (loaded goods17 truck5) 0)
	(= (loaded goods18 truck5) 0)
	(at truck5 depot1)
	(= (loaded goods1 truck6) 0)
	(= (loaded goods2 truck6) 0)
	(= (loaded goods3 truck6) 0)
	(= (loaded goods4 truck6) 0)
	(= (loaded goods5 truck6) 0)
	(= (loaded goods6 truck6) 0)
	(= (loaded goods7 truck6) 0)
	(= (loaded goods8 truck6) 0)
	(= (loaded goods9 truck6) 0)
	(= (loaded goods10 truck6) 0)
	(= (loaded goods11 truck6) 0)
	(= (loaded goods12 truck6) 0)
	(= (loaded goods13 truck6) 0)
	(= (loaded goods14 truck6) 0)
	(= (loaded goods15 truck6) 0)
	(= (loaded goods16 truck6) 0)
	(= (loaded goods17 truck6) 0)
	(= (loaded goods18 truck6) 0)
	(at truck6 depot2)
	(= (loaded goods1 truck7) 0)
	(= (loaded goods2 truck7) 0)
	(= (loaded goods3 truck7) 0)
	(= (loaded goods4 truck7) 0)
	(= (loaded goods5 truck7) 0)
	(= (loaded goods6 truck7) 0)
	(= (loaded goods7 truck7) 0)
	(= (loaded goods8 truck7) 0)
	(= (loaded goods9 truck7) 0)
	(= (loaded goods10 truck7) 0)
	(= (loaded goods11 truck7) 0)
	(= (loaded goods12 truck7) 0)
	(= (loaded goods13 truck7) 0)
	(= (loaded goods14 truck7) 0)
	(= (loaded goods15 truck7) 0)
	(= (loaded goods16 truck7) 0)
	(= (loaded goods17 truck7) 0)
	(= (loaded goods18 truck7) 0)
	(at truck7 depot2)
	(= (loaded goods1 truck8) 0)
	(= (loaded goods2 truck8) 0)
	(= (loaded goods3 truck8) 0)
	(= (loaded goods4 truck8) 0)
	(= (loaded goods5 truck8) 0)
	(= (loaded goods6 truck8) 0)
	(= (loaded goods7 truck8) 0)
	(= (loaded goods8 truck8) 0)
	(= (loaded goods9 truck8) 0)
	(= (loaded goods10 truck8) 0)
	(= (loaded goods11 truck8) 0)
	(= (loaded goods12 truck8) 0)
	(= (loaded goods13 truck8) 0)
	(= (loaded goods14 truck8) 0)
	(= (loaded goods15 truck8) 0)
	(= (loaded goods16 truck8) 0)
	(= (loaded goods17 truck8) 0)
	(= (loaded goods18 truck8) 0)
	(at truck8 depot1)
	(= (loaded goods1 truck9) 0)
	(= (loaded goods2 truck9) 0)
	(= (loaded goods3 truck9) 0)
	(= (loaded goods4 truck9) 0)
	(= (loaded goods5 truck9) 0)
	(= (loaded goods6 truck9) 0)
	(= (loaded goods7 truck9) 0)
	(= (loaded goods8 truck9) 0)
	(= (loaded goods9 truck9) 0)
	(= (loaded goods10 truck9) 0)
	(= (loaded goods11 truck9) 0)
	(= (loaded goods12 truck9) 0)
	(= (loaded goods13 truck9) 0)
	(= (loaded goods14 truck9) 0)
	(= (loaded goods15 truck9) 0)
	(= (loaded goods16 truck9) 0)
	(= (loaded goods17 truck9) 0)
	(= (loaded goods18 truck9) 0)
	(at truck9 depot3)
	(= (stored goods1) 0)
	(= (stored goods2) 0)
	(= (stored goods3) 0)
	(= (stored goods4) 0)
	(= (stored goods5) 0)
	(= (stored goods6) 0)
	(= (stored goods7) 0)
	(= (stored goods8) 0)
	(= (stored goods9) 0)
	(= (stored goods10) 0)
	(= (stored goods11) 0)
	(= (stored goods12) 0)
	(= (stored goods13) 0)
	(= (stored goods14) 0)
	(= (stored goods15) 0)
	(= (stored goods16) 0)
	(= (stored goods17) 0)
	(= (stored goods18) 0)
	(= (total-cost) 0)
	(= (rebate-rate market1) 0.86)
	(= (rebate-rate market2) 0.84)
	(= (rebate-rate market3) 0.78)
	(= (rebate-rate market4) 0.79)
	(= (rebate-rate market5) 0.86)
	(= (rebate-rate market6) 0.79)
	(= (rebate-rate market7) 0.75)
	(= (rebate-rate market8) 0.86)
	(= (rebate-rate market9) 0.76)
	(= (bought goods1) 0)
	(= (bought goods2) 0)
	(= (bought goods3) 0)
	(= (bought goods4) 0)
	(= (bought goods5) 0)
	(= (bought goods6) 0)
	(= (bought goods7) 0)
	(= (bought goods8) 0)
	(= (bought goods9) 0)
	(= (bought goods10) 0)
	(= (bought goods11) 0)
	(= (bought goods12) 0)
	(= (bought goods13) 0)
	(= (bought goods14) 0)
	(= (bought goods15) 0)
	(= (bought goods16) 0)
	(= (bought goods17) 0)
	(= (bought goods18) 0)
	(= (request goods1) 32)
	(= (request goods2) 8)
	(= (request goods3) 21)
	(= (request goods4) 22)
	(= (request goods5) 40)
	(= (request goods6) 1)
	(= (request goods7) 16)
	(= (request goods8) 9)
	(= (request goods9) 28)
	(= (request goods10) 10)
	(= (request goods11) 9)
	(= (request goods12) 32)
	(= (request goods13) 21)
	(= (request goods14) 4)
	(= (request goods15) 18)
	(= (request goods16) 64)
	(= (request goods17) 3)
	(= (request goods18) 43))

(:goal (and
	(>= (stored goods1) (request goods1))
	(>= (stored goods2) (request goods2))
	(>= (stored goods3) (request goods3))
	(>= (stored goods4) (request goods4))
	(>= (stored goods5) (request goods5))
	(>= (stored goods6) (request goods6))
	(>= (stored goods7) (request goods7))
	(>= (stored goods8) (request goods8))
	(>= (stored goods9) (request goods9))
	(>= (stored goods10) (request goods10))
	(>= (stored goods11) (request goods11))
	(>= (stored goods12) (request goods12))
	(>= (stored goods13) (request goods13))
	(>= (stored goods14) (request goods14))
	(>= (stored goods15) (request goods15))
	(>= (stored goods16) (request goods16))
	(>= (stored goods17) (request goods17))
	(>= (stored goods18) (request goods18))))

(:metric minimize (+ (* 1.3 (total-cost))(total-time)))
)