select STATES
exec
 < 'com @ Cell | << 'message ; undef >> % NoClause >
 < 'stop @ Cell | NoCVPair %
                 ('e [ nil ] : 'not [ 'find [ 'None3 ] ] := 'output [ 'resume ] ,
                       'subst_cell [ 'stop , 'proceed ])
                 ('e [ nil ] := 'name [ 'M ] , 'output [ 'waiting [ 'M ] ]) >
 < 'proceed @ Cell | NoCVPair %
                     ('e [ nil ] : 'loc [ 5 ] := 'name [ 'M ] ,
                                   'output [ 'want-enter [ 'M ] ] ,
                                   'subst-cell [ 'proceed , 'want ])
                     ('e [ nil ] : 'loc [ 8 ] := 'name [ 'M ] ,
                                   'output [ 'finished [ 'M ] ] ,
                                   'cv-take [ 'M , 'loc , 'None1 ] ,
                                   'cv-take [ 'M , 'iloc , 'None2 ] ,
                                   'die [ nil ])
                     ('e [ nil ] := 'inc [ 'loc ] , 'loc [ 'L ] , 'name [ 'M ] ,
                             'output [ 'at [ 'M , 'L ] ]) >
 < 'want @ Cell | NoCVPair %
                   ('e [ nil ] : 'find [ 'entered ] := 'output [ 'someone-there ] ,
                        'subst-cell [ 'want , 'stop ])
                   ('e [ nil ] := 'enter [ nil ] , 'subst-cell [ 'want , 'enter ])
                   ('enter [ nil ] := 'name [ 'M ] , 'output [ 'entering [ 'M ] ] ,
                                      'message [ 'entered ] ,
                                       'cv-set [ 'M , 'iloc , 1 ]) >
 < 'enter @ Cell | NoCVPair %
                   ('e [ nil ] : 'iloc [ 3 ] := 'name [ 'M ] ,
                                 'output [ 'exiting [ 'M ] ] ,
                                 'succeed [ 'cv-take [ 'com , 'message , 'None ] ] ,
                                 'inc [ 'loc ] , 'subst-cell [ 'enter , 'proceed ])
                   ('e [ nil ] := 'inc [ 'iloc ] , 'iloc [ 'LL ] , 'name [ 'M ] ,
                                  'output [ 'inside [ 'M , 'LL ] ]) > 
 < 'display @ Cell | NoCVPair % NoClause >
 < 'stdlib @ Cell | NoCVPair % 
                    ('once [ 'Goal ] :  'Goal  , ! )
                    ('succeed [ 'Goal ] : 'Goal  , !)
                    ('succedd [ 'None4 ] : True )
                    ('not [ 'Goal ] : 'once [ 'Goal ] := fail )
                    ('not [ 'None5 ] : True )
                    ('or [ 'goals [ 'X ] , 'goals [ 'Y ] ] : 'X )
                    ('or [ 'goals [ 'X ] , 'goals [ 'Y ] ] : 'Y )
                    ('repeat [ 'Goal ] : 'repeat-try [ 'Goal ] , fail)
                    ('repeat-try [ 'Goal ] : 'not [ 'Goal ] := fail)
                    ('repeat-try [ 'Goal ] : ! , 'repeat-try [ 'Goal ]) >
  < 'main @ Cell | NoCVPair % 
                   ('test [ nil ] := 'fork [ 'agent [ 'a , 1 ] ] ,
                         'fork [ 'agent [ 'b , 1 ] ])
                   ('agent [ 'M , 'Loc ] := 'new-cell [ 'M , 'loc , 'iloc ] ,
                         'push [ 'M ] , 
                         'or [ 'goals [ 'name [ 'M ] ] ,
                               'goals [  'assert [ 'name [ 'M ] ] ] ] ,
                         'cv-write [ 'M , 'loc , 'Loc ] ,
                         'push [ 'proceed ] ,
                         'output [ 'initializing [ 'M , 'Loc ] ] ,
                         'repeat [ 'e [ nil ] ])
                   ('find [ 'Mode ] := 
                         'cv-ref [ 'com , 'message , 'pair [ 'Name , 'Mode ] ],
                         'name [ 'M ] , 'not [ 'eq [ 'Name , 'M ] ])
                   ('message [ 'Mes ] := 'name [ 'M ] ,
                         'cv-write [ 'com , 'message , 'pair [ 'M , 'Mes ] ] ,
                         'output [ 'pair [ 'M , 'Mes ] ])
                   ('loc [ 'L ] := 'name [ 'M ] , 'cv-read [ 'M , 'loc , 'L ])
                   ('iloc [ 'LL ] := 'name [ 'M ] , 'cv-read [ 'M , 'iloc , 'LL ])
                   ('decr [ 'V ] : 'name [ 'M ] , 'cv-take [ 'M , 'V , 'L ] :=
                         'sub [ 'L , 1 , 'L1 ] , 'cv-set [ 'M , 'V , 'L1 ])
                   ('inc [ 'V ] : 'name [ 'M ] , 'cv-take [ 'M , 'V , 'LV ] :=
                         'add [ 'LV , 1 , 'L1 ] , 'cv-set [ 'M , 'V , 'L1 ])
                   ('output [ 'M ] := 'write [ 'M ] , nl ) >
  < 'system-cell @ Cell | << 'a ; 'newa >> << 'b ; 'newb >> %
                                     ('cell [ 'proceed ] := True)
                                     ('cell [ 'want ] := True)
                                     ('cell [ 'enter ] := True)
                                     ('cell [ 'stop ] := True)
                                     ('cell [ 'main ] := True)
                                     ('cell [ 'stdlib ] := True)
                                     ('cell [ 'system-cell ] := True)
                                     ('process [ 'main ] := True) >
  < 'main @ Process | 'main 'stdlib 'system-cell %
                      << 'main ; 1 ; 1 >> % 'test [ nil ], nil % Empty > .
