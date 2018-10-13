module Main

%include javascript "pong_helper.js"

syntax inlineJS [code] = foreign FFI_JS code (JS_IO ())
syntax jsVar [name] [type] = foreign FFI_JS name (JS_IO type)

%inline
jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_JS [] ty} -> ty
jscall fname ty = foreign FFI_JS fname ty

record Paddle where
  constructor MkP
  pCenter, pHeight: Double

record Ball where
  constructor MkB
  bCenter: (Double, Double)
  bRad: Double
  velocity: (Double, Double)

record PongState where
  constructor MkSt
  ball: Ball
  fieldSize: (Double, Double)
  left: Paddle
  right: Paddle

record PongParams where
  constructor MkPms
  aiSpeed, twistFactor, paddleHeight,
  paddleWidth, accelFactor, vx0Factor, vy0Factor: Double

data Side : Type

data Phase = Playing | ShowScore | Waiting | Menu | Attract
data Game : Phase -> Type where
  Play : PongParams -> PongState -> (Int, Int) -> Game Playing
  Report : Side -> PongParams -> (Int, Int) -> (duration : Int) -> Game ShowScore
  Wait : PongParams -> PongState -> (Int, Int) -> (duration : Int) -> Game Waiting
  Choose : Game Menu
  Demo : PongParams -> PongState -> (repetitions : Int) -> Game Attract
  DemoWait : (duration : Int) -> (repetitions : Int) -> Game Waiting

-- Functions for manipulating the game state
record InputState where
  constructor MkI
  mouseY: Double
  escape: Bool

getInputState : JS_IO InputState
getInputState = pure (MkI !getMouse !getEscape) where
  getMouse = jsVar "mouseY" Double
  getEscape = do
    val <- map (== 1) $ jsVar "escape" Int
    foreign FFI_JS "escape = %0" (Int -> JS_IO ()) 0
    pure val

partial
boundVelocity : Double -> (Double, Double) -> Double -> Double
boundVelocity x (lower, upper) = case (x <= upper, x >= lower) of
  (True, True) => id
  (True, False) => abs
  (False, True) => negate . abs
  -- (False, False) => believe_me impossible

collides : PongParams -> Ball -> Paddle -> Paddle -> Double -> Ball
collides pms b (MkP pyl phl) (MkP pyr phr) pxr' = record { bCenter = newP, velocity = newV } b where
  x : Double
  x = fst (bCenter b)
  y : Double
  y = snd (bCenter b)
  pw : Double
  pw = paddleWidth pms
  pxl : Double
  pxl = 0
  pxr : Double
  pxr = pxr' - pw
  left : Bool
  left = y <= pyl + phl/2 && y >= pyl - phl/2 && x - bRad b <= pxl + pw && x + bRad b >= pxl
  right : Bool
  right = y <= pyr + phr/2 && y >= pyr - phr/2 && x - bRad b <= pxr + pw && x + bRad b >= pxr
  newX : Double
  newX = if left then pxl + pw + bRad b
                 else (if right then pxr - bRad b else x)
  newVX : Double
  newVX = if left then abs (fst (velocity b))
                  else (if right then - abs (fst (velocity b)) else fst (velocity b))
  newP = (newX, y)
  vy : Double
  vy = snd (velocity b)
  dvy : Double
  dvy = if left then twistFactor pms * (y - pyl) / phl
                else (if right then twistFactor pms * (y - pyr) / phr else 0)
  factor : Double
  factor = if left || right then accelFactor pms / (1 + abs dvy) else 0
  newV = (newVX + factor * newVX/abs newVX, vy + dvy)

data Outcome = HumanWins | AIWins | Quit

data Side = Human | AI
aiChasePos : PongParams -> Paddle -> Double -> Side -> Ball -> Double
aiChasePos pms rightPaddle w side (MkB (x, y) r (vx, vy)) = 
  if isn'tLazy side w x
    then pCenter rightPaddle + pvy
    else pCenter rightPaddle + pvy*abs pvy/(speed*speed)
 where boundMagnitude : Double -> Double -> Double
       boundMagnitude mag val = min mag (max (-mag) (mag * val))
       speed : Double
       speed = aiSpeed pms
       pvy = boundMagnitude speed ((y - pCenter rightPaddle) / pHeight rightPaddle)
       isn'tLazy : Side -> Double -> Double -> Bool
       isn'tLazy AI w x = x > 3*w/4
       isn'tLazy Human w x = x < w/4
aiTrack : PongParams -> Paddle -> Double -> Ball -> Paddle
aiTrack pms rightPaddle w b = record { pCenter = aiChasePos pms rightPaddle w AI b } rightPaddle

step : PongParams -> Double -> InputState -> PongState -> Either Outcome PongState
step pms deltaT (MkI mouseY esc) (MkSt (MkB (x, y) r (vx, vy)) (w, h) leftPaddle rightPaddle) =
   if esc then Left Quit else Right (MkSt !newBall (w, h) newLeft !newRight)
     where newVY : Double
           newVY = boundVelocity y (0, h) vy
           newVX : Double
           newVX = boundVelocity x (0, w) vx
           newLeft = record { pCenter = mouseY } leftPaddle
           movedBall : Ball
           movedBall = (MkB (x + vx*deltaT, y + vy*deltaT) r (newVX, newVY))
           newBall = if x < 0 || x > w 
                        then (if x < 0 then Left AIWins else Left HumanWins)
                        else Right (collides pms movedBall leftPaddle rightPaddle w)
           newRight = Right (aiTrack pms rightPaddle w !newBall)

-- functions for manipulating the canvas
setFillStyle : String -> JS_IO ()
setFillStyle color = jscall "setFillStyle(%0)" (String -> JS_IO ()) color
clear : String -> JS_IO ()
clear color = do
  setFillStyle color
  inlineJS "context.fillRect(0, 0, canvas.width, canvas.height)"

circle : (Double, Double) -> Double -> JS_IO ()
circle (x, y) rad = do
  inlineJS "context.beginPath()"
  jscall "context.arc(%0, %1, %2, 0, 2*Math.PI, false)" (Double -> Double -> Double -> JS_IO ()) x y rad
  inlineJS "context.fill()"

rect : (Double, Double) -> (Double, Double) -> JS_IO ()
rect (x, y) (w, h) = do
  jscall "context.fillRect(%0, %1, %2, %3)" (Double -> Double -> Double -> Double -> JS_IO ()) x y w h

draw : PongParams -> PongState -> JS_IO ()
draw pms (MkSt (MkB p r v) (w,h) (MkP ly lh) (MkP ry rh)) = do
  clear "#000000"
  setFillStyle "#FFFFFF"
  height <- jsVar "canvas.height" Int
  let pw = paddleWidth pms
  rect (0, ly - lh/2) (pw, lh)
  rect (w-pw, ry - rh/2) (pw, rh)
  circle p 5

newGame : PongParams -> JS_IO PongState
newGame pms = do
  width <- jsVar "canvas.width" Double
  height <- jsVar "canvas.height" Double
  angle <- jscall "Math.random() * 2 * Math.PI" (JS_IO Double)
  vx <- jscall "Math.sin(%0)" (Double -> JS_IO Double) angle
  vy <- jscall "Math.cos(%0)" (Double -> JS_IO Double) angle
  let ball = MkB (width/2, height/2) 4 (vx*vx0Factor pms, vy*vy0Factor pms)
  let paddle = MkP (height/2) (paddleHeight pms)
  pure (MkSt ball (width, height) paddle paddle)

setFont : String -> JS_IO ()
setFont spec =
  jscall "context.font = %0" (String -> JS_IO ()) spec

fillText : String -> (Int, Int) -> JS_IO ()
fillText s (x, y) =
  jscall "context.fillText(%0, %1, %2)" (String -> Int -> Int -> JS_IO ()) s x y

centerText : String -> (pixelSize : Int) -> (family : String) -> 
             (rectTL : (Int, Int)) -> (rectSize : (Int, Int)) ->
             JS_IO ()
centerText str textHeight family (x, y) (w, h) = do
  setFont (show textHeight ++ "px " ++ family)
  textWidth <- measure str
  let dispX = (w - textWidth) `div` 2
  let dispY = (h - textHeight) `div` 2
  fillText str (x + dispX, y + dispY + textHeight)
 where measure : String -> JS_IO Int
       measure str =
         jscall "context.measureText(%0).width" (String -> JS_IO Int) str

drawReport : (Int, Int) -> JS_IO ()
drawReport (h, ai) = do
    clear "#000000"
    setFillStyle "#FFFFFF"
    width <- jsVar "canvas.width" Int
    height <- jsVar "canvas.height" Int
    case (h >= 7, ai >= 7) of
      (False, False) => do
        centerText (show h) 120 "Courier" (0, 0) ((width `div` 2) - 10, height)
        centerText (show ai) 120 "Courier" ((width `div` 2) + 10, 0) ((width `div` 2) - 10, height)
      (True, False) => centerText "Human wins!" 40 "Courier" (0, 0) (width, height)
      (_, True) => centerText "AI wins!" 80 "Courier" (0, 0) (width, height)

setTimeout : (() -> JS_IO ()) -> Double -> JS_IO Int
setTimeout f millis =
    jscall "setTimeout(%0, %1)" (JsFn (() -> JS_IO ()) -> Double -> JS_IO Int) (MkJsFn f) millis

killDemo : JS_IO ()
killDemo = do
  proc <- jsVar "demoProc" Int
  jscall "clearTimeout(%0)" (Int -> JS_IO ()) proc

demoSetTimeout : (() -> JS_IO ()) -> Double -> JS_IO ()
demoSetTimeout f millis = do
  killDemo
  proc <- setTimeout f millis
  jscall "demoProc = %0" (Int -> JS_IO ()) proc

setClick : (() -> JS_IO ()) -> JS_IO ()
setClick f =
  jscall "canvas.onclick = %0" (JsFn (() -> JS_IO ()) -> JS_IO ()) (MkJsFn f)

paramNames : List String
paramNames = ["aiSpeed", "twistFactor", "paddleHeight", "paddleWidth", "accelFactor", "vx0Factor", "vy0Factor"]

readParam : String -> JS_IO (Maybe Double)
readParam name = do
    val <- jscall "document.params[%0].value" (String -> JS_IO String) name
    pure (readNumber val)
  where validDoubleString : Bool -> List Char -> Bool
        validDoubleString False ('.'::xs) = validDoubleString True xs
        validDoubleString True ('.'::xs) = False
        validDoubleString seenDot ('-'::xs) = not ('-' `elem` xs) && validDoubleString seenDot xs
        validDoubleString seenDot (c::xs) = isDigit c && validDoubleString seenDot xs
        validDoubleString _ [] = True
        readNumber : String -> Maybe Double
        readNumber s = if validDoubleString False (unpack s) then Just $ cast s else Nothing

writeParam : String -> Double -> JS_IO ()
writeParam name val =
  jscall "document.params[%0].value = %1" (String -> Double -> JS_IO ()) name val

putParams : PongParams -> JS_IO ()
putParams (MkPms speed twist height width accel vx0 vy0) = do
  writeParam "aiSpeed" speed
  writeParam "twistFactor" twist
  writeParam "paddleHeight" height
  writeParam "paddleWidth" width
  writeParam "accelFactor" accel
  writeParam "vx0Factor" vx0
  writeParam "vy0Factor" vy0

setEnabled : Bool -> String -> JS_IO ()
setEnabled setting name =
  jscall "document.params[%0].disabled = %1 != 1" (String -> Int -> JS_IO ()) name (if setting then 1 else 0)
toggleParamsEnabled : Bool -> JS_IO ()
toggleParamsEnabled setting =
  traverse_ {t = List} (setEnabled setting) 
            ["aiSpeed", "twistFactor", "paddleHeight", "paddleWidth", "accelFactor", "vx0Factor", "vy0Factor"]

getParams : JS_IO (Maybe PongParams)
getParams = do
  speed <- readParam "aiSpeed"
  twist <- readParam "twistFactor"
  height <- readParam "paddleHeight"
  width <- readParam "paddleWidth"
  accel <- readParam "accelFactor"
  vx0 <- readParam "vx0Factor"
  vy0 <- readParam "vy0Factor"
  pure $ [| MkPms speed twist height width accel vx0 vy0 |]

normal : JS_IO Double
normal = pure (!random + !random + !random / 3) where
  subtract : Double -> Double -> Double
  subtract x y = y - x
  random = map ((subtract 1) . (*2)) $ jscall "Math.random()" (JS_IO Double)

randomParams : JS_IO PongParams
randomParams = do
  speed <- maybeParam 10 "aiSpeed"
  twist <- maybeParam 1.3 "aiSpeed"
  height <- maybeParam 50 "paddleHeight"
  width <- maybeParam 7 "paddleWidth"
  accel <- maybeParam 1.25 "accelFactor"
  vx0 <- maybeParam 4 "vx0Factor"
  vy0 <- maybeParam 0.6 "vy0Factor"
  pure (MkPms (max 4 $ speed + !normal*3) (twist + !normal*2)
                (max 10 $ height + !normal*15) (max 3 . abs $ width + !normal*8)
                (max 1 $ accel + !normal*0.1) (vx0 + !normal*1.5)
                (vy0 + !normal))
 where maybeParam : Double -> String -> JS_IO Double
       maybeParam def name = pure def

instructions : JS_IO ()
instructions = do
  width <- jsVar "canvas.width" Int
  height <- jsVar "canvas.height" Int
  centerText "Set the parameters and click here to start." 12 "Lucida Console"
             (0, 3*height`div`4) (width, height`div`4)

showMenu : JS_IO ()
showMenu = do
  clear "black"
  setFillStyle "white"
  width <- jsVar "canvas.width" Int
  height <- jsVar "canvas.height" Int
  centerText "PONG" 120 "Lucida Console" (0, 0) (width, height)
  setFillStyle "white"
  instructions

partial
play : PongParams -> PongState -> (Outcome -> JS_IO ()) -> JS_IO ()
play pms p f = do
  killDemo
  clear "#000000"
  draw pms p
  input <- getInputState
  case (step pms 1 input p) of
    Right next => setTimeout (\() => play pms next f) (1000/60) >>= const (pure ())
    Left winner => f winner

partial
attractPlay : PongParams -> PongState -> (Outcome -> JS_IO ()) -> JS_IO ()
attractPlay pms p f = do
  clear "#000000"
  draw pms p
  width <- jsVar "canvas.width" Int
  height <- jsVar "canvas.height" Int
  setFillStyle "white"
  instructions
  input <- getInputState
  let leftPaddle = left p
  let input' = record { mouseY = aiChasePos pms leftPaddle (cast width) Human (ball p)} input
  case (step pms 1 input' p) of
    Right next => do 
      demoSetTimeout (\() => attractPlay pms next f) (1000/60)
    Left winner => f winner

partial
run : Game phase -> JS_IO ()

startGame : () -> JS_IO ()
startGame _ = do
  killDemo
  pms <- getParams
  toggleParamsEnabled False
  reallyStart pms
 where reallyStart : Maybe PongParams -> JS_IO ()
       reallyStart Nothing = do
         clear "black"
         setFont "12px Lucida Console"
         setFillStyle "white"
         fillText "There was an error in your parameters" (5, 100)
         setTimeout (\_ => run Choose) 3000
         pure ()
       reallyStart (Just pms) = do
         setClick (const (pure ()))
         run (Wait pms !(newGame pms) (0, 0) 2) 

run (Play pms st (h, ai)) = play pms st report where
  report HumanWins = run (Report Human pms (h+1, ai) 2)
  report AIWins = run (Report AI pms (h, ai+1) 2)
  report Quit = run Choose

run (Report winner pms score duration) = do
  drawReport (revert winner score)
  setTimeout (\() => do
    drawReport score
    continueGame) (cast duration * 500)
  pure ()
 where revert : Side -> (Int, Int) -> (Int, Int)
       revert Human (h, ai) = (h-1, ai)
       revert AI (h, ai) = (h, ai-1)
       continueGame : JS_IO ()
       continueGame = do
         st <- newGame pms
         setTimeout (\() => if fst score >= 7 || snd score >= 7
                               then run Choose
                               else run (Wait pms st score 2))
                    (cast duration * 500)
         pure ()

run (Wait pms st score duration) = do
  draw pms st
  setTimeout (\() => run (Play pms st score)) (cast duration * 1000)
  pure ()

run Choose = do
  demoSetTimeout (\() => run (DemoWait 2 3)) 10000
  toggleParamsEnabled True
  showMenu
  setClick startGame

run (Demo pms st reps) = do 
    attractPlay pms st next 
  where next Quit = run Choose
        next _ = if reps == 0 then run Choose else run (DemoWait 2 (reps-1))

run (DemoWait duration reps) = do
    pms <- randomParams
    putParams pms
    toggleParamsEnabled False
    st <- newGame pms
    draw pms st
    instructions
    demoSetTimeout (\() => run (Demo pms st reps)) (cast duration*1000)

partial
main : JS_IO ()
main = run Choose
