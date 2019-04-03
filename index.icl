module index

import StdGeneric
import StdEnum
import Expr
import evalTask
import StdDebug
import getArduinoCode

import iTasks._Framework.Generic
from iTasks import always, hasValue, >>-, :: TaskValue(..), :: Task, :: Stability, :: TaskCont(..), :: Action, updateInformation, 
		viewInformation, class descr, instance descr String, :: UpdateOption, :: ViewOption(..), -||-, -&&-, -||, ||-, startEngine, 
		class Publishable, >>*, class TFunctor, instance TFunctor Task, class TApplicative, instance TApplicative Task, 
		instance Publishable Task, Void
import qualified iTasks

derive class iTask ATaskInputType
derive class iTask ATask


// TIMER CODE
PrintMinAndSec :: Expr (ATask (String, Int, Int) Void)
PrintMinAndSec = task "PrintMinAndSec" [AtString "mode", AtInt "m", AtInt "s"] :=. print (
		mode ++. (str " ") ++. (intVar "m") ++. (str ":") ++. (intVar "s") ++. (str "        ")
	) (integer 0) (integer 0)
where
	mode :: (Expr String)
	mode = variable "mode"

PrintRuningTime :: Expr (ATask Int Void)
PrintRuningTime = task "PrintRuningTime" [AtInt "ts"] (
		runTask PrintMinAndSec (tuple3 (str "Left: ", restMinute, restSec))
	)
where
	restSec = restTime -. (restMinute *. (integer 60))
	restMinute = restTime /. (integer 60)
	restTime = (intVar "ts")

PrintRuningTimeLoop :: Expr (ATask (Int, Int) Int)
PrintRuningTimeLoop = task "PrintRuningTimeLoop" [AtInt "bPressed", AtInt "ts"] :=. 
	If ((ts >=. (intVar "ts")) ||. ((intVar "bPressed")==. buttonReset))
		(integer 0)
		((PrintRuningTime >>|. PrintRuningTimeLoop) (intVar "ts" -. ts, tuple2 (getButtonPressed, intVar "ts"), forgetLeftResult))
where
	ts = getTimestamp

LaunchRuningTimeLoop :: Expr (ATask (Int, Int) Int)
LaunchRuningTimeLoop = task "LaunchRuningTimeLoop" [AtInt "m", AtInt "s"] (runTask PrintRuningTimeLoop (
		tuple2 (
			integer 0,
			getTimestamp +. (((intVar "m") *. (integer 60)) +. (intVar "s"))
			)
	))

SetTime :: Expr (ATask (Int, Int) Int)
SetTime = task "SetTime" [AtInt "m", AtInt "s"] :=. (
		(PrintMinAndSec >>|. SetTimeLoop) (i2, i, forgetLeftResult)
	)
where
	i2 = tuple3 (str "Set:", intVar "m", intVar "s")
	i = tuple2 (intVar "m", intVar "s")


incrSeconds = task "incrRight" [AtInt "L", AtInt "R"] :=. (tuple2 ((intVar "L") +. m, s))
where
	s = vv -. m *. (integer 60)
	m = vv /. (integer 60)
	vv = (intVar "R") +. (integer 1)

SetTimeChangeValue :: Expr (ATask (Int, (Int, Int)) (Int, Int))
SetTimeChangeValue = task "SetTimeChangeValue" [AtInt "bPressed", AtInt "v"]
	(If (bPressed ==. buttonReset) zeroPair  (
		If (bPressed ==. buttonLeft)
			(runTask incrLeft st)
			(
				If (bPressed ==. (buttonRight))
					(runTask incrSeconds st)
				(
					If (bPressed ==. (buttonSelect))
						(ReturnedValue (
							(LaunchRuningTimeLoop >>|. SetTimeChangeValue) (st, x, forgetLeftResult)
						))
						(ReturnedValue st)
				)
			)
	))
where
	bPressed = intVar "bPressed"
	x = tuple2 (integer 0, st)
	zeroPair = ReturnedValue (tuple2 (integer 0, integer 0))
	st :: Expr (Int, Int)
	st = variable "v"


SetTimeLoop :: Expr (ATask (Int, Int) Int)
SetTimeLoop = task "SetTimeLoop" [AtInt "m", AtInt "s"] :=. 
	((waitForAnyButton >>|. SetTime) (integer 0, tuple2 (variable "m", variable "s"), SetTimeChangeValue))


StartTimer :: Expr (ATask Void Int)
StartTimer = task "StartTimer" [AtInt "m"] :=. 
	((PrintMinAndSec >>|. SetTimeLoop) (tuple3 (str "Set:", integer 0, integer 0), tuple2 (integer 0, integer 0), forgetLeftResult))


// COUNTER CODE

PrintScores :: Expr (ATask (Int, Int) Void)
PrintScores = task "PrintScores" [AtInt "l", AtInt "r"] :=. print (
		(str "A:") ++. (stringFrom (intVar "l")) ++. (str " B:") ++. (stringFrom (intVar "r")) ++. (str "        ")
	) (integer 0) (integer 0)

waitForAnyButton :: Expr (ATask Int Int)
waitForAnyButton = task "waitForAnyButton" [AtInt "b"] :=. (getButtonPressedBlocking)


intVar :: String -> (Expr Int)
intVar s = variable s 

incrLeft 	= task "incrLeft" [AtInt "L", AtInt "R"] :=. (tuple2 ((intVar "L") +. (integer 1), (intVar "R")))
incrRight 	= task "incrRight" [AtInt "L", AtInt "R"] :=. (tuple2 ((intVar "L"), (intVar "R") +. (integer 1)))

increment :: Expr (ATask (Int, (Int, Int)) (Int, Int))
increment = task "increment" [AtInt "bPressed", AtInt "counters"]// :=. counters
	(If (bPressed ==. buttonReset) zeroPair  (
		If (bPressed ==. buttonLeft)
			(runTask incrLeft counters)
			(
				If (bPressed ==. (buttonRight))
					(runTask incrRight counters)
					(ReturnedValue counters)
			)
	))
where
	bPressed = intVar "bPressed"
	zeroPair = ReturnedValue (tuple2 (integer 0, integer 0))
	counters :: Expr (Int, Int)
	counters = variable "counters"

PrintScoresAndLoop :: Expr (ATask (Int, Int) Int)
PrintScoresAndLoop = task "PrintScoresAndLoop" [AtInt "countL", AtInt "countR"] :=. (
		(PrintScores >>|. loop) (count, count, forgetLeftResult)
	)
where
	count = tuple2 (intVar "countL", intVar "countR")

loop :: Expr (ATask (Int, Int) Int)
loop = task "loop" [AtInt "count"] :=. 
	((waitForAnyButton >>|. PrintScoresAndLoop) (integer 0, variable "count", increment))

teamsCounter :: Expr (ATask Int Int)
teamsCounter = task "teamsCounter" [AtInt "x"] :=. (
		(PrintScores >>|. loop) (pair, pair, forgetLeftResult)
	)
where
	pair = tuple2 (integer 0, integer 0)

// Start = getArduinoCode (teamsCounter)

Start :: *World -> *World
Start world = startEngine ('iTasks'.tbind ('iTasks'.enterChoice "Select example to run:" [] ["Timer", "Counter"]) run) world
run :: String -> (Task Void)
run "Timer" = runITaskSimulation StartTimer
run _ = runITaskSimulation teamsCounter