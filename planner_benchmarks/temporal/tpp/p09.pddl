(define (problem pfile09)
(:domain TPP-MetricTime)
(:objects
	market1 market2 market3 - market
	depot1 - depot
	truck1 truck2 truck3 - truck
	goods1 goods2 goods3 goods4 goods5 goods6 goods7 goods8 goods9 - goods)

(:init
	(= (price goods1 market1) 49)
	(= (ready-to-load goods1 market1) 0)
	(= (on-sale goods1 market1) 17)
	(= (ready-to-load goods1 market2) 0)
	(= (on-sale goods1 market2) 0)
	(= (price goods1 market3) 26)
	(= (ready-to-load goods1 market3) 0)
	(= (on-sale goods1 market3) 14)
	(= (ready-to-load goods2 market1) 0)
	(= (on-sale goods2 market1) 0)
	(= (ready-to-load goods2 market2) 0)
	(= (on-sale goods2 market2) 0)
	(= (price goods2 market3) 30)
	(= (ready-to-load goods2 market3) 0)
	(= (on-sale goods2 market3) 7)
	(= (price goods3 market1) 29)
	(= (ready-to-load goods3 market1) 0)
	(= (on-sale goods3 market1) 14)
	(= (price goods3 market2) 14)
	(= (ready-to-load goods3 market2) 0)
	(= (on-sale goods3 market2) 4)
	(= (price goods3 market3) 37)
	(= (ready-to-load goods3 market3) 0)
	(= (on-sale goods3 market3) 14)
	(= (price goods4 market1) 43)
	(= (ready-to-load goods4 market1) 0)
	(= (on-sale goods4 market1) 2)
	(= (price goods4 market2) 33)
	(= (ready-to-load goods4 market2) 0)
	(= (on-sale goods4 market2) 9)
	(= (price goods4 market3) 9)
	(= (ready-to-load goods4 market3) 0)
	(= (on-sale goods4 market3) 20)
	(= (price goods5 market1) 15)
	(= (ready-to-load goods5 market1) 0)
	(= (on-sale goods5 market1) 18)
	(= (price goods5 market2) 11)
	(= (ready-to-load goods5 market2) 0)
	(= (on-sale goods5 market2) 15)
	(= (price goods5 market3) 25)
	(= (ready-to-load goods5 market3) 0)
	(= (on-sale goods5 market3) 2)
	(= (ready-to-load goods6 market1) 0)
	(= (on-sale goods6 market1) 0)
	(= (ready-to-load goods6 market2) 0)
	(= (on-sale goods6 market2) 0)
	(= (price goods6 market3) 47)
	(= (ready-to-load goods6 market3) 0)
	(= (on-sale goods6 market3) 3)
	(= (price goods7 market1) 24)
	(= (ready-to-load goods7 market1) 0)
	(= (on-sale goods7 market1) 11)
	(= (price goods7 market2) 32)
	(= (ready-to-load goods7 market2) 0)
	(= (on-sale goods7 market2) 16)
	(= (price goods7 market3) 1)
	(= (ready-to-load goods7 market3) 0)
	(= (on-sale goods7 market3) 12)
	(= (price goods8 market1) 18)
	(= (ready-to-load goods8 market1) 0)
	(= (on-sale goods8 market1) 6)
	(= (price goods8 market2) 33)
	(= (ready-to-load goods8 market2) 0)
	(= (on-sale goods8 market2) 10)
	(= (price goods8 market3) 42)
	(= (ready-to-load goods8 market3) 0)
	(= (on-sale goods8 market3) 8)
	(= (price goods9 market1) 1)
	(= (ready-to-load goods9 market1) 0)
	(= (on-sale goods9 market1) 2)
	(= (price goods9 market2) 13)
	(= (ready-to-load goods9 market2) 0)
	(= (on-sale goods9 market2) 12)
	(= (price goods9 market3) 26)
	(= (ready-to-load goods9 market3) 0)
	(= (on-sale goods9 market3) 16)
	(connected market1 market2)
	(connected market2 market1)
	(= (drive-cost market1 market2) 234.00)
	(= (drive-cost market2 market1) 234.00)
	(= (drive-time market1 market2) 702.00)
	(= (drive-time market2 market1) 702.00)
	(connected market1 market3)
	(connected market3 market1)
	(= (drive-cost market1 market3) 83.00)
	(= (drive-cost market3 market1) 83.00)
	(= (drive-time market1 market3) 249.00)
	(= (drive-time market3 market1) 249.00)
	(connected market2 market3)
	(connected market3 market2)
	(= (drive-cost market2 market3) 880.00)
	(= (drive-cost market3 market2) 880.00)
	(= (drive-time market2 market3) 2640.00)
	(= (drive-time market3 market2) 2640.00)
	(connected depot1 market2)
	(connected market2 depot1)
	(= (drive-cost market2 depot1) 317.00)
	(= (drive-cost depot1 market2) 317.00)
	(= (drive-time market2 depot1) 951.00)
	(= (drive-time depot1 market2) 951.00)
	(= (loaded goods1 truck1) 0)
	(= (loaded goods2 truck1) 0)
	(= (loaded goods3 truck1) 0)
	(= (loaded goods4 truck1) 0)
	(= (loaded goods5 truck1) 0)
	(= (loaded goods6 truck1) 0)
	(= (loaded goods7 truck1) 0)
	(= (loaded goods8 truck1) 0)
	(= (loaded goods9 truck1) 0)
	(at truck1 depot1)
	(= (loaded goods1 truck2) 0)
	(= (loaded goods2 truck2) 0)
	(= (loaded goods3 truck2) 0)
	(= (loaded goods4 truck2) 0)
	(= (loaded goods5 truck2) 0)
	(= (loaded goods6 truck2) 0)
	(= (loaded goods7 truck2) 0)
	(= (loaded goods8 truck2) 0)
	(= (loaded goods9 truck2) 0)
	(at truck2 depot1)
	(= (loaded goods1 truck3) 0)
	(= (loaded goods2 truck3) 0)
	(= (loaded goods3 truck3) 0)
	(= (loaded goods4 truck3) 0)
	(= (loaded goods5 truck3) 0)
	(= (loaded goods6 truck3) 0)
	(= (loaded goods7 truck3) 0)
	(= (loaded goods8 truck3) 0)
	(= (loaded goods9 truck3) 0)
	(at truck3 depot1)
	(= (stored goods1) 0)
	(= (stored goods2) 0)
	(= (stored goods3) 0)
	(= (stored goods4) 0)
	(= (stored goods5) 0)
	(= (stored goods6) 0)
	(= (stored goods7) 0)
	(= (stored goods8) 0)
	(= (stored goods9) 0)
	(= (total-cost) 0)
	(= (rebate-rate market1) 0.76)
	(= (rebate-rate market2) 0.80)
	(= (rebate-rate market3) 0.80)
	(= (bought goods1) 0)
	(= (bought goods2) 0)
	(= (bought goods3) 0)
	(= (bought goods4) 0)
	(= (bought goods5) 0)
	(= (bought goods6) 0)
	(= (bought goods7) 0)
	(= (bought goods8) 0)
	(= (bought goods9) 0)
	(= (request goods1) 11)
	(= (request goods2) 5)
	(= (request goods3) 3)
	(= (request goods4) 19)
	(= (request goods5) 29)
	(= (request goods6) 1)
	(= (request goods7) 7)
	(= (request goods8) 20)
	(= (request goods9) 1))

(:goal (and
	(>= (stored goods1) (request goods1))
	(>= (stored goods2) (request goods2))
	(>= (stored goods3) (request goods3))
	(>= (stored goods4) (request goods4))
	(>= (stored goods5) (request goods5))
	(>= (stored goods6) (request goods6))
	(>= (stored goods7) (request goods7))
	(>= (stored goods8) (request goods8))
	(>= (stored goods9) (request goods9))))

(:metric minimize (+ (* 1.2 (total-cost))(total-time)))
)