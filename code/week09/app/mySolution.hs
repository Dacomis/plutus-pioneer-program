{-# LANGUAGE OverloadedStrings #-}
module Example where

import           Language.Marlowe.Extended

main :: IO ()
main = print . pretty $ contract "Charles" "Simon" "Alex" $ Constant 50


{- Define a contract, Close is the simplest contract which just ends the contract straight away
-}

choiceId :: Party -> ChoiceId
choiceId p = ChoiceId "Winner" p

contract :: Party -> Party -> Party -> Value -> Contract
contract alice bob charlie deposit =
    When
        [ Case
            (Deposit charlie charlie ada $ MulValue deposit $ Constant 2) $
                (When
                    [ f alice bob
                    , f bob alice
                    ]
                10 Close
                )
        ]
        10 Close
    where
        f :: Party -> Party -> Case
        f x y = 
            Case
            (Deposit x x ada deposit)
            (When
                [Case
                    (Deposit y y ada deposit)
                    (When
                        [Case
                            (Choice (choiceId charlie) [Bound 1 2])
                            (If
                                (ValueEQ (ChoiceValue $ choiceId charlie) (Constant 1))
                                (Pay y (Account x) ada deposit Close)
                                (Pay x (Account y) ada deposit Close)
                            )
                        ]
                        30 
                        (Pay charlie (Account alice) ada deposit $
                         Pay charlie (Account bob) ada deposit
                        Close) 
                    )]
                20 Close 
            )