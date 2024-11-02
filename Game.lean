import Game.Levels.Tutorial
import Game.Levels.Add
import Game.Levels.Mul
import Game.Levels.Pow
import Game.Levels.Le
import Game.Levels.MulEX
import Game.Levels.Parity

-- Here's what we'll put on the title screen
Title "自然数ゲーム"
Introduction
"
こんにちは。自然数ゲームへようこそ。
このゲームは、Leanを使って様々な自然数の性質を証明します。
おっと、そんなに身構える必要はありませんよ。
"

Info "
Githubのリンク：https://github.com/csharpython/nat-game-ja
使ったテンプレート：https://github.com/hhu-adam/GameSkeleton
参考と一部コードの元：https://github.com/leanprover-community/NNG4/
Lean jaのDiscord：https://discord.com/invite/p32ZfnVawh
"

/-! Information to be displayed on the servers landing page. -/
Languages "Japanese"
CaptionShort "自然数ゲーム"
CaptionLong "自然数の性質を証明してみましょう"
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
