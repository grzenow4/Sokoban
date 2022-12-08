{-# LANGUAGE OverloadedStrings #-}
import CodeWorld
import Data.String
type Program = IO ()

data Tile = Wall | Ground | Storage | Box | Blank deriving Eq
data Direction = R | U | L | D deriving Eq
data Coord = C Int Int deriving (Eq, Show)
data State = S {
  stPos    :: Coord,
  stDir    :: Direction,
  stBoxes  :: [Coord],
  stLevel  :: Integer,
  stMove   :: Integer
} deriving Eq
data SSState world = StartScreen | Running world
data Activity world = Activity {
  actState  :: world,
  actHandle :: (Event -> world -> world),
  actDraw   ::(world -> Picture)
}
data WithUndo a = WithUndo a [a]
data Maze = Maze Coord (Coord -> Tile)

-- State
initialState = initState 1

initState :: Integer -> State
initState lvl = S start D (initialBoxes m) lvl' 0
  where
    lvl' = if listLength mazes < lvl then 1 else lvl
    m@(Maze start maze) = nth mazes lvl'

-- Coords
initialCoord :: Coord
initialCoord = C 0 0
infoCoord = C 0 8

adjacentCoord :: Direction -> Coord -> Coord
adjacentCoord R (C x y) = C (x + 1) y
adjacentCoord U (C x y) = C x (y + 1)
adjacentCoord L (C x y) = C (x - 1) y
adjacentCoord D (C x y) = C x (y - 1)

adjacentCoords :: (Coord -> Tile) -> Coord -> [Coord]
adjacentCoords maze c = filterList (\x -> maze x /= Wall) [adjacentCoord dir c | dir <- [R, U, L, D]]

moveCoords :: [Direction] -> Coord -> Coord
moveCoords [] c = c
moveCoords (d:ds) c = moveCoords ds (adjacentCoord d c)

isNextCoordFree :: State -> Direction -> Coord -> Bool
isNextCoordFree state dir c = let
    c'            = adjacentCoord dir c
    (Maze _ maze) = getMaze state
    tile          = (addBoxes (stBoxes state) (removeBoxes maze)) c'
  in tile == Ground || tile == Storage

movePlayer :: State -> Direction -> Coord -> State
movePlayer state dir c
    | isNextCoordFree state dir c = moveState
    | elemList c' (stBoxes state) && isNextCoordFree state dir c' = moveStateBox
    | otherwise = state
  where
    c'           = adjacentCoord dir c
    c''          = adjacentCoord dir c'
    moveState    = state { stPos = c', stDir = dir, stMove = (stMove state) + 1 }
    moveStateBox = state {
      stPos = c',
      stDir = dir,
      stBoxes = map (\x -> if x == c' then c'' else x) (stBoxes state),
      stMove = (stMove state) + 1
    }

initialBoxes :: Maze -> [Coord]
initialBoxes m@(Maze _ maze) = filterList (\x -> maze x == Box) (allTiles m)

-- Drawing
drawTile :: Tile -> Picture
drawTile Wall    = wall
drawTile Ground  = ground
drawTile Storage = storage
drawTile Box     = box
drawTile Blank   = blank

pictureOfMaze :: Maze -> Picture
pictureOfMaze m@(Maze _ maze) = pictures(mapList (\x -> atCoord x (drawTile (removeBoxes maze x))) (allTiles m))

atCoord :: Coord -> Picture -> Picture
atCoord (C x y) pic = translated (fromIntegral x) (fromIntegral y) pic

drawState :: State -> Picture
drawState state = atCoord (stPos state) (player2 (stDir state))
                & atCoord initialCoord (pictureOfMaze (getMaze state))

player2 :: Direction -> Picture
player2 R = playerR
player2 U = playerU
player2 L = playerL
player2 D = playerD

pictureOfBoxes :: [Coord] -> Picture
pictureOfBoxes coords = pictures(mapList (\x -> atCoord x (drawTile Box)) coords)

draw :: State -> Picture
draw state = case isWinning state of
  True -> winningScreen (stMove state)
  False -> atCoord (stPos state) (player2 (stDir state))
         & pictureOfBoxes (stBoxes state)
         & atCoord initialCoord (pictureOfMaze (getMaze state))
         & atCoord infoCoord (levelInfo (stLevel state) (stMove state))

-- Maze
removeBoxes :: (Coord -> Tile) -> (Coord -> Tile)
removeBoxes maze = f . maze
  where f tile = if tile == Box then Ground else tile

addBoxes :: [Coord] -> (Coord -> Tile) -> (Coord -> Tile)
addBoxes [] maze c = maze c
addBoxes (c:cs) maze c'
  | c == c'   = Box
  | otherwise = addBoxes cs maze c'

isClosed :: Maze -> Bool
isClosed (Maze start maze) = isGraphClosed start (adjacentCoords maze) (\x -> maze x /= Blank)

isSane :: Maze -> Bool
isSane m@(Maze start maze) = listLength storages >= listLength boxes
  where
    storages = filterList (\x -> maze x == Storage) tiles
    boxes = filterList (\x -> maze x == Box) tiles
    tiles = filterList (\x -> reachable x start (adjacentCoords maze)) (allTiles m)

getMaze :: State -> Maze
getMaze state = nth mazes (stLevel state)

getBoxes :: Maze -> [Coord]
getBoxes m@(Maze start maze) = filterList (\x -> maze x == Box) (allTiles m)

getStorages :: Maze -> [Coord]
getStorages m@(Maze start maze) = filterList (\x -> maze x == Storage) (allTiles m)

-- List functions
elemList :: Eq a => a -> [a] -> Bool
elemList el lst = foldList (\x acc -> x == el || acc) False lst

appendList :: [a] -> [a] -> [a]
appendList x y = foldList (\x acc -> x : acc) y x

listLength :: [a] -> Integer
listLength lst = foldList (\x acc -> acc + 1) 0 lst

filterList :: (a -> Bool) -> [a] -> [a]
filterList f lst = foldList (\x acc -> if f x then x : acc else acc) [] lst

nth :: [a] -> Integer -> a
nth (x:xs) n = snd (
  foldList (\x (n, acc) -> if n == 1 then (n - 1, x) else (n - 1, acc))
  (n, x)
  (x:xs))

mapList :: (a -> b) -> [a] -> [b]
mapList f lst = foldList (\x acc -> (f x) : acc) [] lst

andList :: [Bool] -> Bool
andList lst = foldList (\x acc -> x && acc) True lst

allList :: (a -> Bool) -> [a] -> Bool
allList f lst = foldList (\x acc -> f x && acc) True lst

foldList :: (a -> b -> b) -> b -> [a] -> b
foldList _ acc [] = acc
foldList f acc (x:xs) = f x (foldList f acc xs)

-- Graph functions
isGraphClosed :: Eq a => a -> (a -> [a]) -> (a -> Bool) -> Bool
isGraphClosed initial neighbours isOk = check [] [initial]
  where
    check _       []                    = True
    check _       (x:xs) | not (isOk x) = False
    check visited (x:xs)
      | elemList x visited = check visited xs
      | otherwise          = check (x:visited) (appendList (neighbours x) xs)

reachable :: Eq a => a -> a -> (a -> [a]) -> Bool
reachable v initial neighbours = not (isGraphClosed initial neighbours (\x -> x /= v))

allReachable :: Eq a => [a] -> a -> (a -> [a]) -> Bool
allReachable vs initial neighbours = foldList (\x acc -> (reachable x initial neighbours) && acc) True vs

allTiles :: Maze -> [Coord]
allTiles (Maze start maze) = visit [] [start]
  where
    visit visited [] = visited
    visit visited (x:xs) | elemList x visited = visit visited xs
    visit visited (x:xs) = let neighbours = filterList (\x -> maze x /= Blank) [adjacentCoord dir x | dir <- [R, U, L, D]]
      in visit (x:visited) (appendList neighbours xs)

-- Handling Events
handleEvent :: Event -> State -> State
handleEvent (KeyPress key) state
  | key == "N" = initState (stLevel state + 1)
  | key == "B" = initState (if stLevel state == 1 then listLength mazes else stLevel state - 1)
  | key == "R" = initState (stLevel state)
  | key == "Esc" && isWinning state = initialState
  | isWinning state = state
  | key == "Right" || key == "D" = movePlayer state R (stPos state)
  | key == "Up"    || key == "W" = movePlayer state U (stPos state)
  | key == "Left"  || key == "A" = movePlayer state L (stPos state)
  | key == "Down"  || key == "S" = movePlayer state D (stPos state)
handleEvent _ state = state

handleEventEsc :: world -> (Event -> world -> world) -> Event -> world -> world
handleEventEsc initialState eventHandler (KeyPress key) state
  | key == "Esc" = initialState
  | otherwise    = eventHandler (KeyPress key) state
handleEventEsc initialState eventHandler event state = eventHandler event state

-- Activities
resettable :: Activity s -> Activity s
resettable (Activity initialState handleEvent drawState)
  = Activity initialState handleEvent' drawState
  where handleEvent' (KeyPress key) _ | key == "Esc" = initialState
        handleEvent' e s = handleEvent e s

withStartScreen :: Activity s -> Activity (SSState s)
withStartScreen (Activity initialState handleEvent drawState)
  = Activity initialState' handleEvent' drawState'
  where
    initialState' = StartScreen

    handleEvent' (KeyPress key) StartScreen
         | key == " "                  = Running initialState
    handleEvent' _         StartScreen = StartScreen
    handleEvent' e         (Running s) = Running (handleEvent e s)

    drawState' StartScreen = startScreen
    drawState' (Running s) = drawState s

withUndo :: Eq a => Activity a -> Activity (WithUndo a)
withUndo (Activity initialState handleEvent drawState) = Activity initialState' handleEvent' drawState' where
    initialState' = WithUndo initialState []
    handleEvent' (KeyPress key) (WithUndo s stack) | key == "U"
      = case stack of s':stack' -> WithUndo s' stack'
                      []        -> WithUndo s []
    handleEvent' e         (WithUndo s stack)
       | s' == s = WithUndo s stack
       | otherwise = WithUndo (handleEvent e s) (s:stack)
      where s' = handleEvent e s
    drawState' (WithUndo s _) = drawState s

runActivity :: Activity s -> IO ()
runActivity (Activity initialState handleEvent drawState)
  = activityOf initialState handleEvent drawState

sokobanActivity :: Activity State
sokobanActivity = Activity initialState handleEvent draw

-- Winning
isWinning :: State -> Bool
isWinning state = allList (\x -> elemList x (stBoxes state)) (getStorages (getMaze state))

-- Walking
walk1, walk2, walk3, walk4, etap5 :: IO ()
walk1 = activityOf initialState handleEvent drawState
walk2 = runActivity sokobanActivity
walk3 = runActivity (resettable sokobanActivity)
walk4 = runActivity (withStartScreen (withUndo (resettable sokobanActivity)))
etap5 = walk4

-- Main
main :: Program
main = etap5

-- Pictures
wall, ground, storage, box, playerR, playerU, playerL, playerD, startScreen :: Picture
winningScreen :: Integer -> Picture
levelInfo :: Integer -> Integer -> Picture

wall = bricks & colored grey (solidRectangle 1 1)
bricks = translated (-0.25) 0.375 brick & translated 0.25 0.375 brick
       & translated (-0.25) (-0.125) brick & translated 0.25 (-0.125) brick
       & polyline [(-0.25, 0.25), (-0.25, 0)] & polyline [(0.25, 0.25), (0.25, 0)]
       & polyline [(-0.25, -0.25), (-0.25, -0.5)] & polyline [(0.25, -0.25), (0.25, -0.5)]
brick = rectangle 0.5 0.25

ground = colored (dark white) (solidRectangle 1 1)

storage = colored red x & ground
x = thickPolyline 0.1 [(-0.3, -0.3), (0.3, 0.3), (0, 0), (-0.3, 0.3), (0.3, -0.3)]
   & translated (-0.3) 0.3 end & translated 0.3 0.3 end
   & translated (-0.3) (-0.3) end & translated 0.3 (-0.3) end
end = solidCircle 0.05

box = polyline [(-0.35, 0.25), (0.25, -0.35)] & polyline [(-0.25, 0.35), (0.35, -0.25)]
    & polyline [(-0.35, -0.25), (-0.1, 0)] & polyline [(-0.25, -0.35), (0, -0.1)]
    & polyline [(0, 0.1), (0.25, 0.35)] & polyline [(0.1, 0), (0.35, 0.25)]
    & rectangle 0.7 0.70 & rectangle 1 1 & colored brown (solidRectangle 1 1)

playerR = hat & footR & eyeR & upper & (translated 0 (-0.15) arm) & lower & footL
playerU = hat & pockets & body & arms & feet
playerL = hat & footL & eyeL & upper & (translated 0 (-0.15) arm) & lower & footR
playerD = hat & feet & eyes & arms & body

hat = translated 0 0.17 (colored yellow (sector pi 0 0.3))

body = upper & lower
upper = translated 0 0.15 (colored (light orange) (solidCircle 0.25))
lower = translated 0 (-0.1) (colored blue (solidCircle 0.3))

pockets = translated (-0.1) (-0.27) (rotated (-pi*1/8) pocket) & translated 0.1 (-0.27) (rotated (pi*1/8) pocket)
pocket = rotated pi (colored (light blue) (scaled 1 1.5 (sector pi 0 0.05)))

arms = translated (-0.3) (-0.15) arm & translated 0.3 (-0.15) arm
arm = translated 0 (-0.1) (colored (light orange) (solidCircle 0.08))
    & colored (light blue) (scaled 1 2 (solidCircle 0.08))

eyes = eyeL & eyeR
eyeL = translated (-0.1) 0.13 eye
eyeR = translated 0.1 0.13 eye
eye = scaled 1 2 (solidCircle 0.06)

feet = translated (-0.12) (-0.4) foot & translated 0.12 (-0.4) foot
footL = translated (-0.18) (-0.33) (rotated (-pi*1/6) foot)
footR = translated 0.18 (-0.33) (rotated (pi*1/6) foot)
foot = scaled 1.3 1 (solidCircle 0.08)

startScreen = scaled 3 3 (lettering "Sokoban!")
winningScreen moves = lettering ("Poziom ukończony, liczba ruchów: " <> fromString (show moves))
levelInfo lvl moves = lettering ("Poziom " <> fromString (show lvl) <> ", liczba ruchów: " <> fromString (show moves))

-- Mazes
maze1 :: (Coord -> Tile)
maze1 (C x y)
    | y > 3 || y < -2 = Blank
    | x > 4 || x < -4 = Blank
    | x == -2 && y == -1 = Storage
    | x == 0 && y == -1 = Storage
    | x == 2 && y == 0 = Box
    | x == 2 && y == 1 = Box
    | x >= -4 && x <= 4 && y >= -2 && y <= -2 = Wall
    | x >= -4 && x <= -4 && y >= -1 && y <= 3 = Wall
    | x >= -3 && x <= -2 && y >= 2 && y <= 3 = Wall
    | x >= -2 && x <= -2 && y >= 0 && y <= 0 = Wall
    | x >= -1 && x <= 4 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 1 && y >= -1 && y <= 0 = Wall
    | x >= 1 && x <= 4 && y >= 2 && y <= 2 = Wall
    | x >= 4 && x <= 4 && y >= -1 && y <= 1 = Wall
    | otherwise = Ground

maze2 :: (Coord -> Tile)
maze2 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 4 || x < -3 = Blank
    | x == 0 && y == -1 = Storage
    | x == 2 && y == -1 = Storage
    | x == 0 && y == 1 = Storage
    | x == 2 && y == 1 = Storage
    | x == 1 && y == -1 = Box
    | x == 0 && y == 0 = Box
    | x == 2 && y == 0 = Box
    | x == 1 && y == 1 = Box
    | x >= -3 && x <= 4 && y >= -3 && y <= -3 = Wall
    | x >= -3 && x <= -3 && y >= -2 && y <= 3 = Wall
    | x >= -2 && x <= -2 && y >= 0 && y <= 3 = Wall
    | x >= -1 && x <= 4 && y >= 3 && y <= 3 = Wall
    | x >= 4 && x <= 4 && y >= -2 && y <= 2 = Wall
    | otherwise = Ground

maze3 :: (Coord -> Tile)
maze3 (C x y)
    | y > 3 || y < -2 = Blank
    | x > 6 || x < -5 = Blank
    | x == 0 && y == 0 = Storage
    | x == 1 && y == 0 = Storage
    | x == 2 && y == 0 = Storage
    | x == -3 && y == 0 = Box
    | x == -3 && y == 1 = Box
    | x == -2 && y == 1 = Box
    | x >= -5 && x <= 6 && y >= -2 && y <= -2 = Wall
    | x >= -5 && x <= -5 && y >= -1 && y <= 3 = Wall
    | x >= -4 && x <= 0 && y >= 3 && y <= 3 = Wall
    | x >= -1 && x <= 6 && y >= -1 && y <= -1 = Wall
    | x >= -1 && x <= -1 && y >= 0 && y <= 0 = Wall
    | x >= 0 && x <= 2 && y >= 2 && y <= 2 = Wall
    | x >= 2 && x <= 6 && y >= 3 && y <= 3 = Wall
    | x >= 4 && x <= 4 && y >= 1 && y <= 1 = Wall
    | x >= 6 && x <= 6 && y >= 0 && y <= 2 = Wall
    | otherwise = Ground

maze4 :: (Coord -> Tile)
maze4 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 3 || x < -3 = Blank
    | x == 0 && y == -1 = Storage
    | x == -1 && y == 0 = Storage
    | x == 1 && y == 0 = Storage
    | x == 0 && y == 1 = Storage
    | x == -1 && y == 2 = Storage
    | x == 1 && y == 2 = Storage
    | x == -1 && y == -1 = Box
    | x == 1 && y == -1 = Box
    | x == 0 && y == 0 = Box
    | x == -1 && y == 1 = Box
    | x == 1 && y == 1 = Box
    | x == 0 && y == 2 = Box
    | x >= -3 && x <= -3 && y >= -3 && y <= 4 = Wall
    | x >= -2 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -2 && x <= 3 && y >= 4 && y <= 4 = Wall
    | x >= 3 && x <= 3 && y >= -2 && y <= 3 = Wall
    | otherwise = Ground

maze5 :: (Coord -> Tile)
maze5 (C x y)
    | y > 6 || y < -5 = Blank
    | x > 4 || x < -3 = Blank
    | x == 1 && y == 5 = Storage
    | x == 2 && y == 5 = Storage
    | x == 1 && y == 4 = Box
    | x == 2 && y == 4 = Box
    | x >= -3 && x <= -3 && y >= -5 && y <= 6 = Wall
    | x >= -2 && x <= 4 && y >= -5 && y <= -5 = Wall
    | x >= -2 && x <= -1 && y >= -4 && y <= -4 = Wall
    | x >= -2 && x <= -1 && y >= 0 && y <= 6 = Wall
    | x >= -1 && x <= -1 && y >= -2 && y <= -2 = Wall
    | x >= 0 && x <= 0 && y >= 0 && y <= 3 = Wall
    | x >= 0 && x <= 4 && y >= 6 && y <= 6 = Wall
    | x >= 1 && x <= 1 && y >= -3 && y <= -3 = Wall
    | x >= 2 && x <= 4 && y >= -1 && y <= 3 = Wall
    | x >= 3 && x <= 4 && y >= -4 && y <= -2 = Wall
    | x >= 4 && x <= 4 && y >= 4 && y <= 5 = Wall
    | otherwise = Ground

maze6 :: (Coord -> Tile)
maze6 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 3 || x < -2 = Blank
    | x == 2 && y == -2 = Storage
    | x == -1 && y == 2 = Storage
    | x == 0 && y == 1 = Box
    | x == 1 && y == 1 = Box
    | x >= -2 && x <= 0 && y >= -3 && y <= -1 = Wall
    | x >= -2 && x <= -2 && y >= 0 && y <= 3 = Wall
    | x >= -1 && x <= -1 && y >= 0 && y <= 0 = Wall
    | x >= -1 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= 1 && x <= 1 && y >= -2 && y <= -2 = Wall
    | x >= 2 && x <= 3 && y >= 2 && y <= 2 = Wall
    | x >= 3 && x <= 3 && y >= -2 && y <= 1 = Wall
    | otherwise = Ground

maze7 :: (Coord -> Tile)
maze7 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 5 || x < -5 = Blank
    | x == 2 && y == 1 = Storage
    | x == 2 && y == 2 = Storage
    | x == 2 && y == 3 = Storage
    | x == -1 && y == 0 = Box
    | x == 1 && y == 0 = Box
    | x == 3 && y == 0 = Box
    | x >= -5 && x <= 5 && y >= -3 && y <= -3 = Wall
    | x >= -5 && x <= -5 && y >= -2 && y <= 4 = Wall
    | x >= -4 && x <= 1 && y >= 1 && y <= 4 = Wall
    | x >= -3 && x <= -3 && y >= -1 && y <= -1 = Wall
    | x >= -1 && x <= -1 && y >= -1 && y <= -1 = Wall
    | x >= 1 && x <= 1 && y >= -1 && y <= -1 = Wall
    | x >= 2 && x <= 5 && y >= 4 && y <= 4 = Wall
    | x >= 3 && x <= 5 && y >= -2 && y <= -1 = Wall
    | x >= 3 && x <= 3 && y >= 1 && y <= 2 = Wall
    | x >= 5 && x <= 5 && y >= 0 && y <= 3 = Wall
    | otherwise = Ground

maze8 :: (Coord -> Tile)
maze8 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 4 || x < -4 = Blank
    | x == -2 && y == 0 = Storage
    | x == -1 && y == 0 = Storage
    | x == 2 && y == 0 = Box
    | x == 2 && y == 1 = Box
    | x >= -4 && x <= 4 && y >= -3 && y <= -3 = Wall
    | x >= -4 && x <= -4 && y >= -2 && y <= 4 = Wall
    | x >= -3 && x <= -2 && y >= 1 && y <= 4 = Wall
    | x >= -1 && x <= 4 && y >= -2 && y <= -2 = Wall
    | x >= -1 && x <= 4 && y >= 4 && y <= 4 = Wall
    | x >= 0 && x <= 0 && y >= 0 && y <= 2 = Wall
    | x >= 1 && x <= 1 && y >= 2 && y <= 2 = Wall
    | x >= 3 && x <= 4 && y >= 2 && y <= 3 = Wall
    | x >= 4 && x <= 4 && y >= -1 && y <= 1 = Wall
    | otherwise = Ground

maze9 :: (Coord -> Tile)
maze9 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 4 || x < -4 = Blank
    | x == 1 && y == -1 = Storage
    | x == 1 && y == 0 = Storage
    | x == -1 && y == 1 = Box
    | x == -2 && y == 2 = Box
    | x >= -4 && x <= -2 && y >= -3 && y <= 0 = Wall
    | x >= -4 && x <= -4 && y >= 1 && y <= 4 = Wall
    | x >= -3 && x <= -3 && y >= 1 && y <= 1 = Wall
    | x >= -3 && x <= 4 && y >= 4 && y <= 4 = Wall
    | x >= -1 && x <= 4 && y >= -3 && y <= -3 = Wall
    | x >= -1 && x <= -1 && y >= 0 && y <= 0 = Wall
    | x >= 0 && x <= 4 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 4 && y >= 1 && y <= 2 = Wall
    | x >= 2 && x <= 2 && y >= -1 && y <= -1 = Wall
    | x >= 4 && x <= 4 && y >= -2 && y <= 0 = Wall
    | otherwise = Ground

maze10 :: (Coord -> Tile)
maze10 (C x y)
    | y > 4 || y < -4 = Blank
    | x > 3 || x < -3 = Blank
    | x == -2 && y == 1 = Storage
    | x == -2 && y == 2 = Storage
    | x == -2 && y == 3 = Storage
    | x == 0 && y == -1 = Box
    | x == -1 && y == 0 = Box
    | x == 0 && y == 1 = Box
    | x >= -3 && x <= -2 && y >= -4 && y <= 0 = Wall
    | x >= -3 && x <= -3 && y >= 1 && y <= 4 = Wall
    | x >= -2 && x <= 3 && y >= 4 && y <= 4 = Wall
    | x >= -1 && x <= 3 && y >= -4 && y <= -4 = Wall
    | x >= 0 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= 1 && x <= 3 && y >= 0 && y <= 2 = Wall
    | x >= 3 && x <= 3 && y >= -2 && y <= -1 = Wall
    | otherwise = Ground

maze11 :: (Coord -> Tile)
maze11 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 5 || x < -4 = Blank
    | x == -1 && y == -2 = Storage
    | x == -3 && y == 0 = Storage
    | x == -1 && y == 0 = Storage
    | x == 2 && y == -1 = Box
    | x == 3 && y == -1 = Box
    | x == 3 && y == 0 = Box
    | x >= -4 && x <= 5 && y >= -3 && y <= -3 = Wall
    | x >= -4 && x <= -4 && y >= -2 && y <= 4 = Wall
    | x >= -3 && x <= -3 && y >= 1 && y <= 4 = Wall
    | x >= -2 && x <= 5 && y >= 4 && y <= 4 = Wall
    | x >= -1 && x <= 0 && y >= 1 && y <= 1 = Wall
    | x >= 0 && x <= 0 && y >= -2 && y <= 0 = Wall
    | x >= 0 && x <= 5 && y >= 3 && y <= 3 = Wall
    | x >= 3 && x <= 5 && y >= 2 && y <= 2 = Wall
    | x >= 4 && x <= 5 && y >= 0 && y <= 1 = Wall
    | x >= 5 && x <= 5 && y >= -2 && y <= -1 = Wall
    | otherwise = Ground

maze12 :: (Coord -> Tile)
maze12 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 3 || x < -2 = Blank
    | x == -1 && y == 1 = Storage
    | x == 0 && y == 1 = Storage
    | x == 1 && y == 1 = Storage
    | x == -1 && y == 0 = Box
    | x == 0 && y == 0 = Box
    | x == 1 && y == 0 = Box
    | x >= -2 && x <= -2 && y >= -3 && y <= 3 = Wall
    | x >= -1 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -1 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 2 && x <= 3 && y >= 0 && y <= 2 = Wall
    | x >= 3 && x <= 3 && y >= -2 && y <= -1 = Wall
    | otherwise = Ground

maze13 :: (Coord -> Tile)
maze13 (C x y)
    | y > 4 || y < -4 = Blank
    | x > 3 || x < -3 = Blank
    | x == -2 && y == 2 = Storage
    | x == 0 && y == 2 = Storage
    | x == 0 && y == -1 = Box
    | x == 0 && y == 0 = Box
    | x >= -3 && x <= -1 && y >= -4 && y <= -1 = Wall
    | x >= -3 && x <= -3 && y >= 0 && y <= 4 = Wall
    | x >= -2 && x <= 3 && y >= 4 && y <= 4 = Wall
    | x >= -1 && x <= 0 && y >= 1 && y <= 1 = Wall
    | x >= 0 && x <= 3 && y >= -4 && y <= -4 = Wall
    | x >= 2 && x <= 3 && y >= -3 && y <= 1 = Wall
    | x >= 3 && x <= 3 && y >= 2 && y <= 3 = Wall
    | otherwise = Ground

maze14 :: (Coord -> Tile)
maze14 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 4 || x < -3 = Blank
    | x == 1 && y == 3 = Storage
    | x == 2 && y == 3 = Storage
    | x == 1 && y == 2 = Box
    | x == 2 && y == 2 = Box
    | x >= -3 && x <= 0 && y >= -3 && y <= 1 = Wall
    | x >= -3 && x <= -3 && y >= 2 && y <= 4 = Wall
    | x >= -2 && x <= 4 && y >= 4 && y <= 4 = Wall
    | x >= 1 && x <= 4 && y >= -3 && y <= -3 = Wall
    | x >= 1 && x <= 1 && y >= 1 && y <= 1 = Wall
    | x >= 3 && x <= 4 && y >= -2 && y <= 1 = Wall
    | x >= 4 && x <= 4 && y >= 2 && y <= 3 = Wall
    | otherwise = Ground

maze15 :: (Coord -> Tile)
maze15 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 4 || x < -4 = Blank
    | x == 2 && y == 2 = Storage
    | x == 3 && y == 2 = Storage
    | x == 0 && y == 2 = Box
    | x == 1 && y == 2 = Box
    | x >= -4 && x <= -2 && y >= -3 && y <= 1 = Wall
    | x >= -4 && x <= -4 && y >= 2 && y <= 4 = Wall
    | x >= -3 && x <= 4 && y >= 4 && y <= 4 = Wall
    | x >= -1 && x <= 4 && y >= -3 && y <= -3 = Wall
    | x >= -1 && x <= -1 && y >= 1 && y <= 1 = Wall
    | x >= 1 && x <= 4 && y >= -2 && y <= -1 = Wall
    | x >= 1 && x <= 2 && y >= 1 && y <= 1 = Wall
    | x >= 2 && x <= 4 && y >= 3 && y <= 3 = Wall
    | x >= 4 && x <= 4 && y >= 0 && y <= 2 = Wall
    | otherwise = Ground

maze16 :: (Coord -> Tile)
maze16 (C x y)
    | y > 3 || y < -2 = Blank
    | x > 3 || x < -3 = Blank
    | x == -1 && y == 1 = Storage
    | x == 1 && y == 1 = Storage
    | x == -1 && y == 0 = Box
    | x == 0 && y == 0 = Box
    | x >= -3 && x <= 3 && y >= -2 && y <= -2 = Wall
    | x >= -3 && x <= -3 && y >= -1 && y <= 3 = Wall
    | x >= -2 && x <= -2 && y >= -1 && y <= -1 = Wall
    | x >= -2 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 0 && x <= 3 && y >= 2 && y <= 2 = Wall
    | x >= 1 && x <= 1 && y >= 0 && y <= 0 = Wall
    | x >= 3 && x <= 3 && y >= -1 && y <= 1 = Wall
    | otherwise = Ground

maze17 :: (Coord -> Tile)
maze17 (C x y)
    | y > 4 || y < -4 = Blank
    | x > 3 || x < -3 = Blank
    | x == -2 && y == 2 = Storage
    | x == 0 && y == 2 = Storage
    | x == 0 && y == -1 = Box
    | x == 1 && y == -1 = Box
    | x >= -3 && x <= -2 && y >= -4 && y <= 0 = Wall
    | x >= -3 && x <= -3 && y >= 1 && y <= 4 = Wall
    | x >= -2 && x <= 3 && y >= 4 && y <= 4 = Wall
    | x >= -1 && x <= 3 && y >= -4 && y <= -4 = Wall
    | x >= 0 && x <= 0 && y >= 0 && y <= 0 = Wall
    | x >= 1 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= 1 && x <= 1 && y >= 1 && y <= 1 = Wall
    | x >= 1 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 3 && x <= 3 && y >= -2 && y <= 2 = Wall
    | otherwise = Ground

maze18 :: (Coord -> Tile)
maze18 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 3 || x < -3 = Blank
    | x == -1 && y == -2 = Storage
    | x == 1 && y == -2 = Storage
    | x == 0 && y == 1 = Box
    | x == 1 && y == 1 = Box
    | x >= -3 && x <= -3 && y >= -3 && y <= 3 = Wall
    | x >= -2 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -2 && x <= -1 && y >= 1 && y <= 2 = Wall
    | x >= -1 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 3 && y >= 0 && y <= 0 = Wall
    | x >= 3 && x <= 3 && y >= -2 && y <= -1 = Wall
    | x >= 3 && x <= 3 && y >= 1 && y <= 2 = Wall
    | otherwise = Ground

maze19 :: (Coord -> Tile)
maze19 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 3 || x < -3 = Blank
    | x == -1 && y == 0 = Storage
    | x == 0 && y == 0 = Storage
    | x == 1 && y == 0 = Storage
    | x == 1 && y == -1 = Box
    | x == 0 && y == 1 = Box
    | x == 1 && y == 1 = Box
    | x >= -3 && x <= -3 && y >= -3 && y <= 3 = Wall
    | x >= -2 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -2 && x <= -2 && y >= 0 && y <= 3 = Wall
    | x >= -1 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 3 && y >= -2 && y <= -2 = Wall
    | x >= 1 && x <= 3 && y >= 2 && y <= 2 = Wall
    | x >= 3 && x <= 3 && y >= -1 && y <= 1 = Wall
    | otherwise = Ground

maze20 :: (Coord -> Tile)
maze20 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 3 || x < -2 = Blank
    | x == 0 && y == 0 = Storage
    | x == 1 && y == 0 = Storage
    | x == 2 && y == 0 = Storage
    | x == 0 && y == -1 = Box
    | x == 1 && y == -1 = Box
    | x == 1 && y == 1 = Box
    | x >= -2 && x <= -2 && y >= -3 && y <= 4 = Wall
    | x >= -1 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -1 && x <= 0 && y >= -2 && y <= -2 = Wall
    | x >= -1 && x <= -1 && y >= 1 && y <= 4 = Wall
    | x >= 0 && x <= 0 && y >= 1 && y <= 1 = Wall
    | x >= 0 && x <= 3 && y >= 4 && y <= 4 = Wall
    | x >= 3 && x <= 3 && y >= -2 && y <= 3 = Wall
    | otherwise = Ground

maze21 :: (Coord -> Tile)
maze21 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 3 || x < -3 = Blank
    | x == -2 && y == -2 = Storage
    | x == 1 && y == 2 = Storage
    | x == 0 && y == 0 = Box
    | x == 1 && y == 0 = Box
    | x >= -3 && x <= -3 && y >= -3 && y <= 3 = Wall
    | x >= -2 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -2 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= -1 && x <= -1 && y >= -1 && y <= -1 = Wall
    | x >= -1 && x <= 0 && y >= 1 && y <= 1 = Wall
    | x >= 1 && x <= 3 && y >= -2 && y <= -2 = Wall
    | x >= 2 && x <= 3 && y >= 1 && y <= 2 = Wall
    | x >= 3 && x <= 3 && y >= -1 && y <= 0 = Wall
    | otherwise = Ground

maze22 :: (Coord -> Tile)
maze22 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 3 || x < -3 = Blank
    | x == -1 && y == -1 = Storage
    | x == 1 && y == -1 = Storage
    | x == -1 && y == 0 = Box
    | x == 0 && y == 0 = Box
    | x >= -3 && x <= -3 && y >= -3 && y <= 3 = Wall
    | x >= -2 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -2 && x <= -2 && y >= -2 && y <= -1 = Wall
    | x >= -2 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 3 && y >= 0 && y <= 2 = Wall
    | x >= 3 && x <= 3 && y >= -2 && y <= -1 = Wall
    | otherwise = Ground

maze23 :: (Coord -> Tile)
maze23 (C x y)
    | y > 4 || y < -4 = Blank
    | x > 5 || x < -5 = Blank
    | x == 3 && y == -2 = Storage
    | x == 3 && y == 0 = Storage
    | x == -3 && y == -1 = Box
    | x == -1 && y == -1 = Box
    | x >= -5 && x <= 5 && y >= -4 && y <= -4 = Wall
    | x >= -5 && x <= -5 && y >= -3 && y <= 4 = Wall
    | x >= -4 && x <= -4 && y >= 0 && y <= 4 = Wall
    | x >= -3 && x <= 2 && y >= -2 && y <= -2 = Wall
    | x >= -3 && x <= 0 && y >= 1 && y <= 4 = Wall
    | x >= 1 && x <= 1 && y >= 1 && y <= 1 = Wall
    | x >= 1 && x <= 5 && y >= 4 && y <= 4 = Wall
    | x >= 2 && x <= 2 && y >= 0 && y <= 0 = Wall
    | x >= 4 && x <= 5 && y >= -3 && y <= -1 = Wall
    | x >= 4 && x <= 5 && y >= 3 && y <= 3 = Wall
    | x >= 5 && x <= 5 && y >= 0 && y <= 2 = Wall
    | otherwise = Ground

maze24 :: (Coord -> Tile)
maze24 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 3 || x < -2 = Blank
    | x == -1 && y == 0 = Storage
    | x == 0 && y == 0 = Storage
    | x == 1 && y == 0 = Storage
    | x == 1 && y == -1 = Box
    | x == 0 && y == 1 = Box
    | x == 1 && y == 1 = Box
    | x >= -2 && x <= -2 && y >= -3 && y <= 3 = Wall
    | x >= -1 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -1 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 3 && y >= 2 && y <= 2 = Wall
    | x >= 2 && x <= 3 && y >= -2 && y <= -2 = Wall
    | x >= 3 && x <= 3 && y >= -1 && y <= 1 = Wall
    | otherwise = Ground

maze25 :: (Coord -> Tile)
maze25 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 3 || x < -3 = Blank
    | x == -1 && y == -1 = Storage
    | x == 1 && y == -1 = Storage
    | x == 1 && y == 1 = Storage
    | x == -1 && y == 0 = Box
    | x == 0 && y == 0 = Box
    | x == 0 && y == 1 = Box
    | x >= -3 && x <= -3 && y >= -3 && y <= 3 = Wall
    | x >= -2 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -2 && x <= -1 && y >= -2 && y <= -2 = Wall
    | x >= -2 && x <= -2 && y >= 1 && y <= 3 = Wall
    | x >= -1 && x <= -1 && y >= 2 && y <= 3 = Wall
    | x >= 0 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 2 && x <= 3 && y >= 1 && y <= 2 = Wall
    | x >= 3 && x <= 3 && y >= -2 && y <= 0 = Wall
    | otherwise = Ground

maze26 :: (Coord -> Tile)
maze26 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 3 || x < -3 = Blank
    | x == -2 && y == -2 = Storage
    | x == -2 && y == 0 = Storage
    | x == -2 && y == 2 = Storage
    | x == 0 && y == -1 = Box
    | x == 0 && y == 0 = Box
    | x == 0 && y == 1 = Box
    | x >= -3 && x <= -3 && y >= -3 && y <= 3 = Wall
    | x >= -2 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -2 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 0 && x <= 0 && y >= -2 && y <= -2 = Wall
    | x >= 0 && x <= 0 && y >= 2 && y <= 2 = Wall
    | x >= 1 && x <= 1 && y >= 0 && y <= 0 = Wall
    | x >= 3 && x <= 3 && y >= -2 && y <= 2 = Wall
    | otherwise = Ground

maze27 :: (Coord -> Tile)
maze27 (C x y)
    | y > 5 || y < -4 = Blank
    | x > 3 || x < -3 = Blank
    | x == -1 && y == -1 = Storage
    | x == -1 && y == 0 = Storage
    | x == -1 && y == 1 = Storage
    | x == -1 && y == 2 = Storage
    | x == -1 && y == 3 = Storage
    | x == 1 && y == -1 = Box
    | x == 0 && y == 0 = Box
    | x == 0 && y == 1 = Box
    | x == 0 && y == 2 = Box
    | x == 1 && y == 3 = Box
    | x >= -3 && x <= -2 && y >= -4 && y <= 5 = Wall
    | x >= -1 && x <= 3 && y >= -4 && y <= -4 = Wall
    | x >= -1 && x <= -1 && y >= -3 && y <= -3 = Wall
    | x >= -1 && x <= -1 && y >= 4 && y <= 5 = Wall
    | x >= 0 && x <= 3 && y >= 5 && y <= 5 = Wall
    | x >= 2 && x <= 3 && y >= -1 && y <= 4 = Wall
    | x >= 3 && x <= 3 && y >= -3 && y <= -2 = Wall
    | otherwise = Ground

maze28 :: (Coord -> Tile)
maze28 (C x y)
    | y > 2 || y < -2 = Blank
    | x > 7 || x < -7 = Blank
    | x == -5 && y == -1 = Storage
    | x == -4 && y == -1 = Storage
    | x == -3 && y == -1 = Storage
    | x == -2 && y == -1 = Storage
    | x == -1 && y == -1 = Storage
    | x == -5 && y == 0 = Box
    | x == -3 && y == 0 = Box
    | x == -1 && y == 0 = Box
    | x == 1 && y == 0 = Box
    | x == 3 && y == 0 = Box
    | x >= -7 && x <= 7 && y >= -2 && y <= -2 = Wall
    | x >= -7 && x <= -7 && y >= -1 && y <= 2 = Wall
    | x >= -6 && x <= 7 && y >= 2 && y <= 2 = Wall
    | x >= -4 && x <= 7 && y >= 1 && y <= 1 = Wall
    | x >= 7 && x <= 7 && y >= -1 && y <= 0 = Wall
    | otherwise = Ground

maze29 :: (Coord -> Tile)
maze29 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 4 || x < -4 = Blank
    | x == 3 && y == 1 = Storage
    | x == 3 && y == 2 = Storage
    | x == 3 && y == 3 = Storage
    | x == -2 && y == 0 = Box
    | x == 1 && y == 0 = Box
    | x == 0 && y == 1 = Box
    | x >= -4 && x <= 0 && y >= -3 && y <= -1 = Wall
    | x >= -4 && x <= -4 && y >= 0 && y <= 4 = Wall
    | x >= -3 && x <= 0 && y >= 3 && y <= 4 = Wall
    | x >= 0 && x <= 2 && y >= 2 && y <= 2 = Wall
    | x >= 1 && x <= 4 && y >= -3 && y <= -3 = Wall
    | x >= 1 && x <= 4 && y >= 4 && y <= 4 = Wall
    | x >= 2 && x <= 2 && y >= -1 && y <= -1 = Wall
    | x >= 2 && x <= 2 && y >= 1 && y <= 1 = Wall
    | x >= 2 && x <= 2 && y >= 3 && y <= 3 = Wall
    | x >= 4 && x <= 4 && y >= -2 && y <= 3 = Wall
    | otherwise = Ground

maze30 :: (Coord -> Tile)
maze30 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 5 || x < -4 = Blank
    | x == -2 && y == -1 = Storage
    | x == 3 && y == 0 = Storage
    | x == 0 && y == 1 = Storage
    | x == 1 && y == -1 = Box
    | x == 0 && y == 0 = Box
    | x == 1 && y == 0 = Box
    | x >= -4 && x <= 0 && y >= -3 && y <= -2 = Wall
    | x >= -4 && x <= -4 && y >= -1 && y <= 3 = Wall
    | x >= -3 && x <= 5 && y >= 3 && y <= 3 = Wall
    | x >= -2 && x <= -2 && y >= 0 && y <= 1 = Wall
    | x >= -1 && x <= -1 && y >= 1 && y <= 1 = Wall
    | x >= 1 && x <= 5 && y >= -3 && y <= -3 = Wall
    | x >= 1 && x <= 3 && y >= 1 && y <= 1 = Wall
    | x >= 2 && x <= 3 && y >= -1 && y <= -1 = Wall
    | x >= 5 && x <= 5 && y >= -2 && y <= 2 = Wall
    | otherwise = Ground

maze31 :: (Coord -> Tile)
maze31 (C x y)
    | y > 4 || y < -4 = Blank
    | x > 5 || x < -4 = Blank
    | x == 2 && y == 0 = Storage
    | x == 2 && y == 2 = Storage
    | x == 1 && y == 0 = Box
    | x == 1 && y == 1 = Box
    | x >= -4 && x <= 5 && y >= -4 && y <= -4 = Wall
    | x >= -4 && x <= -4 && y >= -3 && y <= 4 = Wall
    | x >= -3 && x <= -2 && y >= 0 && y <= 0 = Wall
    | x >= -3 && x <= 5 && y >= 4 && y <= 4 = Wall
    | x >= -2 && x <= -2 && y >= -2 && y <= -2 = Wall
    | x >= -2 && x <= -2 && y >= 2 && y <= 2 = Wall
    | x >= 0 && x <= 5 && y >= -3 && y <= -2 = Wall
    | x >= 0 && x <= 0 && y >= -1 && y <= 0 = Wall
    | x >= 0 && x <= 0 && y >= 2 && y <= 3 = Wall
    | x >= 1 && x <= 5 && y >= 3 && y <= 3 = Wall
    | x >= 3 && x <= 5 && y >= 1 && y <= 2 = Wall
    | x >= 5 && x <= 5 && y >= -1 && y <= 0 = Wall
    | otherwise = Ground

maze32 :: (Coord -> Tile)
maze32 (C x y)
    | y > 3 || y < -2 = Blank
    | x > 4 || x < -3 = Blank
    | x == -1 && y == -1 = Storage
    | x == 2 && y == -1 = Storage
    | x == -1 && y == 0 = Box
    | x == 0 && y == 0 = Box
    | x == 1 && y == 0 = Box
    | x >= -3 && x <= 4 && y >= -2 && y <= -2 = Wall
    | x >= -3 && x <= -3 && y >= -1 && y <= 3 = Wall
    | x >= -2 && x <= -2 && y >= 1 && y <= 3 = Wall
    | x >= -1 && x <= 4 && y >= 3 && y <= 3 = Wall
    | x >= 2 && x <= 4 && y >= 1 && y <= 2 = Wall
    | x >= 3 && x <= 4 && y >= 0 && y <= 0 = Wall
    | x >= 4 && x <= 4 && y >= -1 && y <= -1 = Wall
    | otherwise = Ground

maze33 :: (Coord -> Tile)
maze33 (C x y)
    | y > 3 || y < -2 = Blank
    | x > 4 || x < -3 = Blank
    | x == 1 && y == 0 = Storage
    | x == 2 && y == 0 = Storage
    | x == 3 && y == 0 = Storage
    | x == -1 && y == 1 = Box
    | x == 0 && y == 1 = Box
    | x == 1 && y == 1 = Box
    | x >= -3 && x <= 4 && y >= -2 && y <= -2 = Wall
    | x >= -3 && x <= -3 && y >= -1 && y <= 3 = Wall
    | x >= -2 && x <= -2 && y >= -1 && y <= -1 = Wall
    | x >= -2 && x <= 4 && y >= 3 && y <= 3 = Wall
    | x >= 0 && x <= 0 && y >= 0 && y <= 0 = Wall
    | x >= 3 && x <= 4 && y >= -1 && y <= -1 = Wall
    | x >= 3 && x <= 4 && y >= 1 && y <= 2 = Wall
    | x >= 4 && x <= 4 && y >= 0 && y <= 0 = Wall
    | otherwise = Ground

maze34 :: (Coord -> Tile)
maze34 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 3 || x < -3 = Blank
    | x == 2 && y == -1 = Storage
    | x == 2 && y == 0 = Storage
    | x == 2 && y == 1 = Storage
    | x == 1 && y == -1 = Box
    | x == 1 && y == 0 = Box
    | x == 1 && y == 1 = Box
    | x >= -3 && x <= -3 && y >= -3 && y <= 4 = Wall
    | x >= -2 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -2 && x <= 0 && y >= 1 && y <= 4 = Wall
    | x >= -1 && x <= -1 && y >= -1 && y <= -1 = Wall
    | x >= 1 && x <= 3 && y >= 4 && y <= 4 = Wall
    | x >= 2 && x <= 3 && y >= -2 && y <= -2 = Wall
    | x >= 3 && x <= 3 && y >= -1 && y <= 3 = Wall
    | otherwise = Ground

maze35 :: (Coord -> Tile)
maze35 (C x y)
    | y > 4 || y < -4 = Blank
    | x > 4 || x < -4 = Blank
    | x == 3 && y == -1 = Storage
    | x == 3 && y == 0 = Storage
    | x == 3 && y == 1 = Storage
    | x == -1 && y == -1 = Box
    | x == 0 && y == -1 = Box
    | x == 0 && y == 0 = Box
    | x >= -4 && x <= -4 && y >= -4 && y <= 4 = Wall
    | x >= -3 && x <= 4 && y >= -4 && y <= -4 = Wall
    | x >= -3 && x <= -2 && y >= -3 && y <= -3 = Wall
    | x >= -3 && x <= 1 && y >= 1 && y <= 4 = Wall
    | x >= 1 && x <= 4 && y >= -3 && y <= -2 = Wall
    | x >= 1 && x <= 1 && y >= -1 && y <= -1 = Wall
    | x >= 2 && x <= 4 && y >= 4 && y <= 4 = Wall
    | x >= 4 && x <= 4 && y >= -1 && y <= 3 = Wall
    | otherwise = Ground

maze36 :: (Coord -> Tile)
maze36 (C x y)
    | y > 1 || y < -1 = Blank
    | x > 2 || x < -2 = Blank
    | x == 1 && y == 0 = Storage
    | x == 0 && y == 0 = Box
    | x >= -2 && x <= 2 && y >= -1 && y <= -1 = Wall
    | x >= -2 && x <= -2 && y >= 0 && y <= 1 = Wall
    | x >= -1 && x <= 2 && y >= 1 && y <= 1 = Wall
    | x >= 2 && x <= 2 && y >= 0 && y <= 0 = Wall
    | otherwise = Ground

maze37 :: (Coord -> Tile)
maze37 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 3 || x < -2 = Blank
    | x == -1 && y == 2 = Storage
    | x == 0 && y == 2 = Storage
    | x == 1 && y == 2 = Storage
    | x == 1 && y == -1 = Box
    | x == 1 && y == 0 = Box
    | x == 1 && y == 1 = Box
    | x >= -2 && x <= -2 && y >= -3 && y <= 3 = Wall
    | x >= -1 && x <= 3 && y >= -3 && y <= -3 = Wall
    | x >= -1 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 0 && x <= 0 && y >= 0 && y <= 0 = Wall
    | x >= 2 && x <= 3 && y >= 0 && y <= 0 = Wall
    | x >= 3 && x <= 3 && y >= -2 && y <= -1 = Wall
    | x >= 3 && x <= 3 && y >= 1 && y <= 2 = Wall
    | otherwise = Ground

maze38 :: (Coord -> Tile)
maze38 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 5 || x < -5 = Blank
    | x == -1 && y == -1 = Storage
    | x == 1 && y == -1 = Storage
    | x == -3 && y == 1 = Box
    | x == -1 && y == 1 = Box
    | x >= -5 && x <= -5 && y >= -3 && y <= 3 = Wall
    | x >= -4 && x <= -1 && y >= -3 && y <= -3 = Wall
    | x >= -4 && x <= -3 && y >= 2 && y <= 3 = Wall
    | x >= -3 && x <= -1 && y >= 0 && y <= 0 = Wall
    | x >= -2 && x <= 5 && y >= 3 && y <= 3 = Wall
    | x >= -1 && x <= 1 && y >= -2 && y <= -2 = Wall
    | x >= 1 && x <= 5 && y >= -3 && y <= -3 = Wall
    | x >= 1 && x <= 5 && y >= 0 && y <= 0 = Wall
    | x >= 3 && x <= 5 && y >= 1 && y <= 2 = Wall
    | x >= 5 && x <= 5 && y >= -2 && y <= -1 = Wall
    | otherwise = Ground

maze39 :: (Coord -> Tile)
maze39 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 4 || x < -3 = Blank
    | x == -1 && y == -1 = Storage
    | x == -1 && y == 0 = Storage
    | x == -1 && y == 1 = Storage
    | x == 0 && y == 0 = Box
    | x == 1 && y == 0 = Box
    | x == 2 && y == 0 = Box
    | x >= -3 && x <= -3 && y >= -3 && y <= 4 = Wall
    | x >= -2 && x <= 4 && y >= -3 && y <= -3 = Wall
    | x >= -2 && x <= 0 && y >= -2 && y <= -2 = Wall
    | x >= -2 && x <= 4 && y >= 4 && y <= 4 = Wall
    | x >= 0 && x <= 0 && y >= -1 && y <= -1 = Wall
    | x >= 0 && x <= 0 && y >= 1 && y <= 2 = Wall
    | x >= 2 && x <= 4 && y >= 2 && y <= 3 = Wall
    | x >= 3 && x <= 4 && y >= 1 && y <= 1 = Wall
    | x >= 4 && x <= 4 && y >= -2 && y <= 0 = Wall
    | otherwise = Ground

maze40 :: (Coord -> Tile)
maze40 (C x y)
    | y > 5 || y < -4 = Blank
    | x > 4 || x < -3 = Blank
    | x == -1 && y == -2 = Storage
    | x == 0 && y == -2 = Storage
    | x == 1 && y == -2 = Storage
    | x == -1 && y == 1 = Box
    | x == -1 && y == 2 = Box
    | x == -1 && y == 3 = Box
    | x >= -3 && x <= -3 && y >= -4 && y <= 5 = Wall
    | x >= -2 && x <= 4 && y >= -4 && y <= -4 = Wall
    | x >= -2 && x <= -2 && y >= -3 && y <= 0 = Wall
    | x >= -2 && x <= 4 && y >= 5 && y <= 5 = Wall
    | x >= -1 && x <= -1 && y >= 0 && y <= 0 = Wall
    | x >= 0 && x <= 0 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 1 && y >= -1 && y <= 1 = Wall
    | x >= 2 && x <= 4 && y >= 0 && y <= 4 = Wall
    | x >= 4 && x <= 4 && y >= -3 && y <= -1 = Wall
    | otherwise = Ground

maze41 :: (Coord -> Tile)
maze41 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 5 || x < -4 = Blank
    | x == 3 && y == 1 = Storage
    | x == 4 && y == 1 = Storage
    | x == -2 && y == 0 = Box
    | x == -1 && y == 1 = Box
    | x >= -4 && x <= 5 && y >= -3 && y <= -3 = Wall
    | x >= -4 && x <= -4 && y >= -2 && y <= 3 = Wall
    | x >= -3 && x <= -2 && y >= -2 && y <= -1 = Wall
    | x >= -3 && x <= -2 && y >= 2 && y <= 3 = Wall
    | x >= -1 && x <= 5 && y >= 3 && y <= 3 = Wall
    | x >= 0 && x <= 3 && y >= -1 && y <= -1 = Wall
    | x >= 1 && x <= 5 && y >= 2 && y <= 2 = Wall
    | x >= 3 && x <= 3 && y >= 0 && y <= 0 = Wall
    | x >= 5 && x <= 5 && y >= -2 && y <= 1 = Wall
    | otherwise = Ground

maze42 :: (Coord -> Tile)
maze42 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 6 || x < -5 = Blank
    | x == 3 && y == -1 = Storage
    | x == 3 && y == 0 = Storage
    | x == 3 && y == 1 = Storage
    | x == 3 && y == 2 = Storage
    | x == -2 && y == -1 = Box
    | x == -1 && y == -1 = Box
    | x == -3 && y == 0 = Box
    | x == 0 && y == 0 = Box
    | x >= -5 && x <= 6 && y >= -3 && y <= -3 = Wall
    | x >= -5 && x <= -5 && y >= -2 && y <= 4 = Wall
    | x >= -4 && x <= -4 && y >= -2 && y <= -2 = Wall
    | x >= -4 && x <= -3 && y >= 1 && y <= 4 = Wall
    | x >= -2 && x <= 1 && y >= 2 && y <= 4 = Wall
    | x >= 0 && x <= 2 && y >= 1 && y <= 1 = Wall
    | x >= 1 && x <= 6 && y >= -2 && y <= -2 = Wall
    | x >= 1 && x <= 1 && y >= -1 && y <= -1 = Wall
    | x >= 2 && x <= 6 && y >= 4 && y <= 4 = Wall
    | x >= 5 && x <= 6 && y >= -1 && y <= 0 = Wall
    | x >= 6 && x <= 6 && y >= 1 && y <= 3 = Wall
    | otherwise = Ground

maze43 :: (Coord -> Tile)
maze43 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 5 || x < -4 = Blank
    | x == 3 && y == -1 = Storage
    | x == 4 && y == -1 = Storage
    | x == 1 && y == -1 = Box
    | x == 1 && y == 1 = Box
    | x >= -4 && x <= -2 && y >= -3 && y <= 1 = Wall
    | x >= -4 && x <= -4 && y >= 2 && y <= 4 = Wall
    | x >= -3 && x <= 5 && y >= 4 && y <= 4 = Wall
    | x >= -1 && x <= 5 && y >= -3 && y <= -3 = Wall
    | x >= -1 && x <= 0 && y >= 0 && y <= 1 = Wall
    | x >= 0 && x <= 0 && y >= -2 && y <= -1 = Wall
    | x >= 0 && x <= 0 && y >= 3 && y <= 3 = Wall
    | x >= 3 && x <= 5 && y >= -2 && y <= -2 = Wall
    | x >= 3 && x <= 5 && y >= 0 && y <= 3 = Wall
    | x >= 5 && x <= 5 && y >= -1 && y <= -1 = Wall
    | otherwise = Ground

maze44 :: (Coord -> Tile)
maze44 (C x y)
    | y > 4 || y < -4 = Blank
    | x > 6 || x < -6 = Blank
    | x == 3 && y == -2 = Storage
    | x == 4 && y == -2 = Storage
    | x == 5 && y == -2 = Storage
    | x == -4 && y == -1 = Box
    | x == -3 && y == -1 = Box
    | x == -1 && y == 0 = Box
    | x >= -6 && x <= 6 && y >= -4 && y <= -4 = Wall
    | x >= -6 && x <= -6 && y >= -3 && y <= 4 = Wall
    | x >= -5 && x <= -1 && y >= -3 && y <= -3 = Wall
    | x >= -5 && x <= -4 && y >= -2 && y <= -2 = Wall
    | x >= -5 && x <= 6 && y >= 4 && y <= 4 = Wall
    | x >= -4 && x <= -4 && y >= 0 && y <= 2 = Wall
    | x >= -3 && x <= 2 && y >= 2 && y <= 2 = Wall
    | x >= -1 && x <= -1 && y >= -2 && y <= -1 = Wall
    | x >= 0 && x <= 3 && y >= -1 && y <= -1 = Wall
    | x >= 1 && x <= 1 && y >= -3 && y <= -2 = Wall
    | x >= 3 && x <= 3 && y >= 0 && y <= 0 = Wall
    | x >= 5 && x <= 6 && y >= 2 && y <= 3 = Wall
    | x >= 6 && x <= 6 && y >= -3 && y <= 1 = Wall
    | otherwise = Ground

maze45 :: (Coord -> Tile)
maze45 (C x y)
    | y > 5 || y < -4 = Blank
    | x > 5 || x < -4 = Blank
    | x == 4 && y == -2 = Storage
    | x == 4 && y == -1 = Storage
    | x == 4 && y == 0 = Storage
    | x == 4 && y == 1 = Storage
    | x == 0 && y == -2 = Box
    | x == -2 && y == -1 = Box
    | x == 1 && y == 0 = Box
    | x == 3 && y == 1 = Box
    | x >= -4 && x <= -4 && y >= -4 && y <= 5 = Wall
    | x >= -3 && x <= 5 && y >= -4 && y <= -4 = Wall
    | x >= -3 && x <= -3 && y >= -1 && y <= -1 = Wall
    | x >= -3 && x <= -3 && y >= 3 && y <= 5 = Wall
    | x >= -2 && x <= 5 && y >= 5 && y <= 5 = Wall
    | x >= -1 && x <= -1 && y >= -1 && y <= 3 = Wall
    | x >= 0 && x <= 0 && y >= -3 && y <= -3 = Wall
    | x >= 0 && x <= 0 && y >= -1 && y <= 0 = Wall
    | x >= 0 && x <= 3 && y >= 3 && y <= 3 = Wall
    | x >= 2 && x <= 3 && y >= 0 && y <= 0 = Wall
    | x >= 3 && x <= 3 && y >= -3 && y <= -1 = Wall
    | x >= 3 && x <= 3 && y >= 2 && y <= 2 = Wall
    | x >= 4 && x <= 5 && y >= -3 && y <= -3 = Wall
    | x >= 5 && x <= 5 && y >= -2 && y <= 4 = Wall
    | otherwise = Ground

maze46 :: (Coord -> Tile)
maze46 (C x y)
    | y > 5 || y < -4 = Blank
    | x > 4 || x < -4 = Blank
    | x == 0 && y == -3 = Storage
    | x == -1 && y == 2 = Storage
    | x == 0 && y == 2 = Storage
    | x == 1 && y == 2 = Storage
    | x == -1 && y == -1 = Box
    | x == 0 && y == -1 = Box
    | x == 2 && y == -1 = Box
    | x == 1 && y == 1 = Box
    | x >= -4 && x <= -1 && y >= -4 && y <= -2 = Wall
    | x >= -4 && x <= -4 && y >= -1 && y <= 5 = Wall
    | x >= -3 && x <= 4 && y >= 5 && y <= 5 = Wall
    | x >= -2 && x <= -2 && y >= 0 && y <= 3 = Wall
    | x >= -1 && x <= 0 && y >= 1 && y <= 1 = Wall
    | x >= -1 && x <= 1 && y >= 3 && y <= 3 = Wall
    | x >= 0 && x <= 4 && y >= -4 && y <= -4 = Wall
    | x >= 1 && x <= 4 && y >= -3 && y <= -3 = Wall
    | x >= 2 && x <= 4 && y >= 1 && y <= 1 = Wall
    | x >= 3 && x <= 4 && y >= -2 && y <= -2 = Wall
    | x >= 3 && x <= 4 && y >= 2 && y <= 4 = Wall
    | x >= 4 && x <= 4 && y >= -1 && y <= 0 = Wall
    | otherwise = Ground

maze47 :: (Coord -> Tile)
maze47 (C x y)
    | y > 3 || y < -2 = Blank
    | x > 6 || x < -6 = Blank
    | x == 0 && y == 1 = Storage
    | x == 1 && y == 1 = Storage
    | x == 2 && y == 1 = Storage
    | x == 3 && y == 1 = Storage
    | x == -3 && y == 1 = Box
    | x == -2 && y == 1 = Box
    | x == -1 && y == 1 = Box
    | x == 4 && y == 1 = Box
    | x >= -6 && x <= 6 && y >= -2 && y <= -2 = Wall
    | x >= -6 && x <= -6 && y >= -1 && y <= 3 = Wall
    | x >= -5 && x <= -3 && y >= 2 && y <= 3 = Wall
    | x >= -2 && x <= 1 && y >= -1 && y <= -1 = Wall
    | x >= -2 && x <= 6 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 3 && y >= 0 && y <= 0 = Wall
    | x >= 2 && x <= 3 && y >= 2 && y <= 2 = Wall
    | x >= 3 && x <= 6 && y >= -1 && y <= -1 = Wall
    | x >= 6 && x <= 6 && y >= 0 && y <= 2 = Wall
    | otherwise = Ground

maze48 :: (Coord -> Tile)
maze48 (C x y)
    | y > 3 || y < -2 = Blank
    | x > 9 || x < -9 = Blank
    | x == 1 && y == 0 = Storage
    | x == 1 && y == 2 = Storage
    | x == 2 && y == 0 = Box
    | x == -1 && y == 1 = Box
    | x >= -9 && x <= -7 && y >= -2 && y <= 0 = Wall
    | x >= -9 && x <= -9 && y >= 1 && y <= 3 = Wall
    | x >= -8 && x <= -5 && y >= 3 && y <= 3 = Wall
    | x >= -6 && x <= -4 && y >= -2 && y <= -2 = Wall
    | x >= -5 && x <= -1 && y >= 2 && y <= 2 = Wall
    | x >= -4 && x <= -4 && y >= -1 && y <= 0 = Wall
    | x >= -3 && x <= -1 && y >= 0 && y <= 0 = Wall
    | x >= -1 && x <= 2 && y >= -2 && y <= -2 = Wall
    | x >= -1 && x <= -1 && y >= -1 && y <= -1 = Wall
    | x >= -1 && x <= 9 && y >= 3 && y <= 3 = Wall
    | x >= 2 && x <= 5 && y >= -1 && y <= -1 = Wall
    | x >= 2 && x <= 9 && y >= 1 && y <= 2 = Wall
    | x >= 5 && x <= 9 && y >= -2 && y <= -2 = Wall
    | x >= 9 && x <= 9 && y >= -1 && y <= 0 = Wall
    | otherwise = Ground

maze49 :: (Coord -> Tile)
maze49 (C x y)
    | y > 4 || y < -4 = Blank
    | x > 5 || x < -4 = Blank
    | x == 0 && y == -3 = Storage
    | x == 0 && y == -2 = Storage
    | x == 0 && y == -1 = Storage
    | x == 0 && y == 0 = Storage
    | x == 3 && y == -2 = Box
    | x == -1 && y == 1 = Box
    | x == 0 && y == 1 = Box
    | x == 0 && y == 2 = Box
    | x >= -4 && x <= -1 && y >= -4 && y <= -1 = Wall
    | x >= -4 && x <= -4 && y >= 0 && y <= 4 = Wall
    | x >= -3 && x <= -2 && y >= 0 && y <= 0 = Wall
    | x >= -3 && x <= -3 && y >= 3 && y <= 4 = Wall
    | x >= -2 && x <= 5 && y >= 4 && y <= 4 = Wall
    | x >= 0 && x <= 5 && y >= -4 && y <= -4 = Wall
    | x >= 1 && x <= 1 && y >= -1 && y <= 0 = Wall
    | x >= 2 && x <= 5 && y >= -3 && y <= -3 = Wall
    | x >= 2 && x <= 5 && y >= 0 && y <= 3 = Wall
    | x >= 5 && x <= 5 && y >= -2 && y <= -1 = Wall
    | otherwise = Ground

maze50 :: (Coord -> Tile)
maze50 (C x y)
    | y > 4 || y < -4 = Blank
    | x > 4 || x < -4 = Blank
    | x == -3 && y == -1 = Storage
    | x == -2 && y == -1 = Storage
    | x == -1 && y == -1 = Storage
    | x == 0 && y == -1 = Storage
    | x == -1 && y == 0 = Box
    | x == 1 && y == 0 = Box
    | x == 1 && y == 1 = Box
    | x == 1 && y == 2 = Box
    | x >= -4 && x <= -4 && y >= -4 && y <= 4 = Wall
    | x >= -3 && x <= 4 && y >= -4 && y <= -4 = Wall
    | x >= -3 && x <= -3 && y >= -3 && y <= -3 = Wall
    | x >= -3 && x <= -3 && y >= 0 && y <= 4 = Wall
    | x >= -2 && x <= -2 && y >= 1 && y <= 4 = Wall
    | x >= -1 && x <= 0 && y >= 1 && y <= 1 = Wall
    | x >= -1 && x <= 4 && y >= 4 && y <= 4 = Wall
    | x >= 0 && x <= 0 && y >= -3 && y <= -3 = Wall
    | x >= 1 && x <= 1 && y >= -1 && y <= -1 = Wall
    | x >= 3 && x <= 4 && y >= -1 && y <= 3 = Wall
    | x >= 4 && x <= 4 && y >= -3 && y <= -2 = Wall
    | otherwise = Ground

maze51 :: (Coord -> Tile)
maze51 (C x y)
    | y > 7 || y < -6 = Blank
    | x > 4 || x < -4 = Blank
    | x == -1 && y == -3 = Storage
    | x == 1 && y == -3 = Storage
    | x == 0 && y == 4 = Storage
    | x == -1 && y == -2 = Box
    | x == 1 && y == -2 = Box
    | x == 0 && y == 5 = Box
    | x >= -4 && x <= -4 && y >= -6 && y <= 7 = Wall
    | x >= -3 && x <= -2 && y >= -6 && y <= -3 = Wall
    | x >= -3 && x <= -3 && y >= -2 && y <= -2 = Wall
    | x >= -3 && x <= -3 && y >= 4 && y <= 7 = Wall
    | x >= -2 && x <= -2 && y >= 0 && y <= 2 = Wall
    | x >= -2 && x <= -1 && y >= 5 && y <= 7 = Wall
    | x >= -1 && x <= 4 && y >= -6 && y <= -6 = Wall
    | x >= -1 && x <= -1 && y >= -1 && y <= -1 = Wall
    | x >= -1 && x <= -1 && y >= 3 && y <= 3 = Wall
    | x >= 0 && x <= 4 && y >= 7 && y <= 7 = Wall
    | x >= 1 && x <= 1 && y >= -1 && y <= -1 = Wall
    | x >= 1 && x <= 1 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 4 && y >= 5 && y <= 6 = Wall
    | x >= 2 && x <= 4 && y >= -5 && y <= -3 = Wall
    | x >= 2 && x <= 2 && y >= 0 && y <= 2 = Wall
    | x >= 3 && x <= 4 && y >= -2 && y <= -2 = Wall
    | x >= 3 && x <= 4 && y >= 4 && y <= 4 = Wall
    | x >= 4 && x <= 4 && y >= -1 && y <= 3 = Wall
    | otherwise = Ground

maze52 :: (Coord -> Tile)
maze52 (C x y)
    | y > 3 || y < -3 = Blank
    | x > 5 || x < -4 = Blank
    | x == -2 && y == -2 = Storage
    | x == -2 && y == -1 = Storage
    | x == -2 && y == 0 = Storage
    | x == 0 && y == -1 = Box
    | x == 1 && y == 0 = Box
    | x == 2 && y == 1 = Box
    | x >= -4 && x <= 5 && y >= -3 && y <= -3 = Wall
    | x >= -4 && x <= -4 && y >= -2 && y <= 3 = Wall
    | x >= -3 && x <= -3 && y >= 1 && y <= 3 = Wall
    | x >= -2 && x <= 5 && y >= 3 && y <= 3 = Wall
    | x >= -1 && x <= -1 && y >= -1 && y <= 0 = Wall
    | x >= 0 && x <= 5 && y >= 2 && y <= 2 = Wall
    | x >= 1 && x <= 5 && y >= -2 && y <= -1 = Wall
    | x >= 5 && x <= 5 && y >= 0 && y <= 1 = Wall
    | otherwise = Ground

maze53 :: (Coord -> Tile)
maze53 (C x y)
    | y > 4 || y < -3 = Blank
    | x > 5 || x < -5 = Blank
    | x == -1 && y == -2 = Storage
    | x == -2 && y == 0 = Storage
    | x == 0 && y == 0 = Storage
    | x == 3 && y == -1 = Box
    | x == 2 && y == 0 = Box
    | x == 3 && y == 1 = Box
    | x >= -5 && x <= 5 && y >= -3 && y <= -3 = Wall
    | x >= -5 && x <= -5 && y >= -2 && y <= 4 = Wall
    | x >= -4 && x <= -2 && y >= 4 && y <= 4 = Wall
    | x >= -2 && x <= -1 && y >= -1 && y <= -1 = Wall
    | x >= -2 && x <= -2 && y >= 1 && y <= 3 = Wall
    | x >= -1 && x <= 1 && y >= 3 && y <= 3 = Wall
    | x >= 1 && x <= 1 && y >= -2 && y <= 0 = Wall
    | x >= 1 && x <= 1 && y >= 2 && y <= 2 = Wall
    | x >= 1 && x <= 5 && y >= 4 && y <= 4 = Wall
    | x >= 4 && x <= 5 && y >= 1 && y <= 3 = Wall
    | x >= 5 && x <= 5 && y >= -2 && y <= 0 = Wall
    | otherwise = Ground

maze54 :: (Coord -> Tile)
maze54 (C x y)
    | y > 5 || y < -4 = Blank
    | x > 4 || x < -3 = Blank
    | x == -1 && y == -2 = Storage
    | x == 0 && y == -2 = Storage
    | x == -1 && y == -1 = Storage
    | x == 0 && y == -1 = Storage
    | x == -1 && y == 1 = Box
    | x == -1 && y == 2 = Box
    | x == 1 && y == 2 = Box
    | x == 2 && y == 2 = Box
    | x >= -3 && x <= -3 && y >= -4 && y <= 5 = Wall
    | x >= -2 && x <= 4 && y >= -4 && y <= -4 = Wall
    | x >= -2 && x <= 0 && y >= -3 && y <= -3 = Wall
    | x >= -2 && x <= -2 && y >= -2 && y <= -2 = Wall
    | x >= -2 && x <= -2 && y >= 1 && y <= 1 = Wall
    | x >= -2 && x <= 4 && y >= 5 && y <= 5 = Wall
    | x >= 0 && x <= 1 && y >= 1 && y <= 1 = Wall
    | x >= 1 && x <= 4 && y >= 0 && y <= 0 = Wall
    | x >= 1 && x <= 4 && y >= 4 && y <= 4 = Wall
    | x >= 3 && x <= 4 && y >= -3 && y <= -1 = Wall
    | x >= 4 && x <= 4 && y >= 1 && y <= 3 = Wall
    | otherwise = Ground

badMaze1 :: Coord -> Tile
badMaze1 (C x y)
  | abs x > 4  || abs y > 4  = Blank
  | abs x == 4 || abs y == 4 = Wall
  | x ==  2                  = Wall
  | x ==  3 && y <= 0        = Storage
  | x >= -2 && y == 0        = Box
  | otherwise                = Ground

badMaze2 :: Coord -> Tile
badMaze2 (C x y)
  | abs x > 7 || abs y > 7                            = Blank
  | abs x == 7                                        = Wall
  | abs y == 7                                        = Wall
  | x >= 4 && y == 4                                  = Wall
  | x == 4 && y >= 4                                  = Wall
  | x >= 5 && y >= 5                                  = Storage
  | elem (x, y) [(-6, 6), (-6, -6), (6, -6), (6, -5)] = Storage
  | x == 0 && elem y [-4 .. 2]                        = Box
  | otherwise                                         = Ground

mazes :: [Maze]
mazes = [Maze (C (2) (-1)) maze1, Maze (C (1) (0)) maze2, Maze (C (5) (1)) maze3,
         Maze (C (0) (-2)) maze4, Maze (C (3) (5)) maze5, Maze (C (-1) (1)) maze6,
         Maze (C (-3) (0)) maze7, Maze (C (2) (2)) maze8, Maze (C (0) (0)) maze9,
         Maze (C (-1) (2)) maze10, Maze (C (2) (0)) maze11, Maze (C (0) (2)) maze12,
         Maze (C (0) (-2)) maze13, Maze (C (0) (2)) maze14, Maze (C (-1) (2)) maze15,
         Maze (C (2) (0)) maze16, Maze (C (-1) (-1)) maze17, Maze (C (2) (1)) maze18,
         Maze (C (0) (-1)) maze19, Maze (C (1) (3)) maze20, Maze (C (2) (0)) maze21,
         Maze (C (-1) (1)) maze22, Maze (C (1) (-1)) maze23, Maze (C (0) (-1)) maze24,
         Maze (C (-1) (1)) maze25, Maze (C (2) (0)) maze26, Maze (C (2) (-2)) maze27,
         Maze (C (5) (0)) maze28, Maze (C (1) (-1)) maze29, Maze (C (0) (-1)) maze30,
         Maze (C (1) (-1)) maze31, Maze (C (0) (-1)) maze32, Maze (C (-2) (1)) maze33,
         Maze (C (1) (2)) maze34, Maze (C (3) (3)) maze35, Maze (C (-1) (0)) maze36,
         Maze (C (1) (-2)) maze37, Maze (C (-3) (-1)) maze38, Maze (C (0) (3)) maze39,
         Maze (C (-1) (4)) maze40, Maze (C (2) (1)) maze41, Maze (C (-3) (-1)) maze42,
         Maze (C (-2) (3)) maze43, Maze (C (4) (2)) maze44, Maze (C (-2) (3)) maze45,
         Maze (C (2) (2)) maze46, Maze (C (5) (1)) maze47, Maze (C (7) (0)) maze48,
         Maze (C (3) (-1)) maze49, Maze (C (2) (-2)) maze50, Maze (C (0) (6)) maze51,
         Maze (C (-1) (-2)) maze52, Maze (C (-4) (-1)) maze53, Maze (C (-1) (4)) maze54]

badMazes :: [Maze]
badMazes = [Maze (C (-2) (-2)) badMaze1, Maze (C 1 (-1)) badMaze2]

-- Debug
pictureOfBools :: [Bool] -> Picture
pictureOfBools xs = translated (-fromIntegral k /2) (fromIntegral k) (go 0 xs)
  where n = length xs
        k = findK 0 -- k is the integer square of n
        findK i | i * i >= n = i
                | otherwise  = findK (i+1)
        go _ [] = blank
        go i (b:bs) =
          translated (fromIntegral (i `mod` k))
                     (-fromIntegral (i `div` k))
                     (pictureOfBool b)
          & go (i+1) bs

        pictureOfBool True =  colored green (solidCircle 0.4)
        pictureOfBool False = colored red   (solidCircle 0.4)

etap4 :: Picture
etap4 = pictureOfBools (appendList (map isClosed (appendList mazes badMazes))
                                   (map isSane   (appendList mazes badMazes)))
