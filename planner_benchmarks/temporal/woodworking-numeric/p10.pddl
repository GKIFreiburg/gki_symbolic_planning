; woodworking sawing task with 12 parts
; Machines:
;   3 highspeed-saw
;   1 saw
; random seed: 691421

(define (problem wood-prob)
  (:domain woodworking)
  (:objects
    highspeed-saw0 highspeed-saw1 highspeed-saw2 - highspeed-saw
    saw0 - saw
    black white red green blue mauve - acolour
    mahogany walnut pine - awood
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 - part
    b0 b1 b2 b3 - board
  )
  (:init
    (idle highspeed-saw0)
    (empty highspeed-saw0)
    (idle highspeed-saw1)
    (empty highspeed-saw1)
    (idle highspeed-saw2)
    (empty highspeed-saw2)
    (idle saw0)
    (unused p0)
    (= (goal-size p0) 9)
    (unused p1)
    (= (goal-size p1) 14)
    (unused p2)
    (= (goal-size p2) 6)
    (unused p3)
    (= (goal-size p3) 15)
    (unused p4)
    (= (goal-size p4) 7)
    (unused p5)
    (= (goal-size p5) 7)
    (unused p6)
    (= (goal-size p6) 13)
    (unused p7)
    (= (goal-size p7) 5)
    (unused p8)
    (= (goal-size p8) 11)
    (unused p9)
    (= (goal-size p9) 5)
    (unused p10)
    (= (goal-size p10) 8)
    (unused p11)
    (= (goal-size p11) 8)
    (= (board-size b0) 5)
    (wood b0 mahogany)
    (surface-condition b0 rough)
    (available b0)
    (= (board-size b1) 30)
    (wood b1 pine)
    (surface-condition b1 rough)
    (available b1)
    (= (board-size b2) 44)
    (wood b2 walnut)
    (surface-condition b2 smooth)
    (available b2)
    (= (board-size b3) 29)
    (wood b3 walnut)
    (surface-condition b3 rough)
    (available b3)
  )
  (:goal
    (and
      (available p0)
      (wood p0 walnut)
      (available p1)
      (wood p1 walnut)
      (available p2)
      (available p3)
      (wood p3 walnut)
      (available p4)
      (wood p4 walnut)
      (available p5)
      (wood p5 walnut)
      (available p6)
      (wood p6 walnut)
      (available p7)
      (wood p7 pine)
      (available p8)
      (available p9)
      (wood p9 mahogany)
      (available p10)
      (wood p10 pine)
      (available p11)
      (wood p11 walnut)
    )
  )
  (:metric minimize (total-time))
)
