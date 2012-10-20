-- From: hbh@cas.et.tudelft.nl (Hendrik Hilberdink)
-- Message-Id: <9803311005.AA15222@dutedix.et.tudelft.nl>
-- Subject: The need for memo
-- To: diacon@stoilow.imar.ro (Razvan Diaconescu),
--         sawada@sra.co.jp (Toshimi Sawada)
-- Date: Tue, 31 Mar 1998 12:05:42 +0200 (MET DST)
-- X-Mailer: ELM [version 2.4 PL24]
-- Mime-Version: 1.0
-- Content-Transfer-Encoding: 7bit
-- Content-Type: text/plain; charset=US-ASCII
-- Content-Length: 40618

-- The CafeOBJ code below describes an access control system for
-- CAD frameworks. Design work is carried out in "projects" by 
-- "users" who operate in "teams". Access control - the control 
-- of who has access to which privilege - is effected by assigning
-- privileges to "roles", and by letting users play roles in teams
-- and letting teams play roles in projects. So a user has access
-- to a "framework privilege" if he is a member of a team in which
-- he plays a role which contains that privilege. Also a user has
-- access to a "project privilege" in a project P if he is a member
-- of a team in which he plays a role containing that privilege
-- *and* that team plays a role, containing that privilege, in P. 
-- Finally all the operations to which access is controlled, such 
-- as a user modifying a team or a role, or assigning a role to
-- another user in a team, etc., are defined in the module 
-- ACCESS-CONTROL. Note that the controlled access is expressed
-- by the synchronization in that module.

-- The remaining two files contain the test "environment" 
-- (testacc.mod) and the actual test module (input1.mod). Bear in
-- mind that initial the system contains no teams, only three
-- predefined roles, no projects and no permissions. The operation 
-- 		op U[_] : Int -> UserId	
-- provides an infinite supply of arbitrary users. The operation
-- 	create_singleton-teams : Int -> Acc-Sys
-- creates n teams containing only one member each. The operation
-- op _adds-users_to_given_ : UserId List TeamId Acc-Sys -> Acc-Sys
-- specifies the attempt by a user to add a number of users, 
-- specified by a list, to his team. 

-- In the file input1.mod the operations
-- 	op A[_] : Int -> Acc-Sys .
-- and 
-- 	op A[_,_,_] : Int List Int -> Acc-Sys .
-- describe infinite sequences of access control states. A[n] denotes
-- the state after n singleton teams have been added to the 
-- initial state of the system. A[m,l,n] denotes the state that
-- results when user u[m] attempts to add the users specified by l
-- to his team when the access control state is A[n].

-- The reductions:

-- red U[1] has-access-to < team , modify > given perms A[1] .

-- results in false because A[1] does not contain any teams of which
-- U[1] is a member, let alone has any permissions.

-- red U[0] has-access-to < team , modify > given perms A[1] .

-- results in true because U[0] has just created a team (consisting
-- of himself). This means he plays the role "team-manager" in
-- his own team which contains the framework privilege < team , modify >. 

-- red U[54] is-member-of (initial-team-name U[0]) given A[8] .

-- False because the team named by (initial-team-name U[0]) contains only
-- the user U[0].

-- red U[1] is-member-of (initial-team-name U[0]) given A[0,L2,1] .

-- True because U[0] has added U[1] to his team (his name features on
-- the list L2).

-- red U[2] is-member-of (initial-team-name U[0]) given A[0,L3,1] .

-- Ditto.

-- red U[2] is-member-of (initial-team-name U[0]) given A[0,L3,2] .

-- Ditto.

-- red "Framework Manager" has-access-to < role , create > given init-acc-sys .

-- False. As things stand at the moment the framework manager is no
-- more authorised to do anything than anyone else. That will have to
-- change. 

-- The need for memo:
-- ==================

-- Because of synchronization the equations involving the operation
-- perms (in ACCESS-CONTROL) are of the form:

-- perms (m(Acc-Sys)) = if c(perms(Acc-Sys)) then n(perms(Acc-Sys)) 
-- 			else k(perms(Acc-Sys)) fi

-- where c is a condition, and m, n and k are methods. 
-- So if Acc-Sys is an initial system state with N methods applied to
-- it, it follows that to compute perms(m(Acc-Sys)) requires at least
-- 2^N computations of the form perms(X). In our example, perms A[2]
-- takes 55 rewrites, perms A[4] takes 335 rewrites, perms A[8] takes
-- 7063 rewrites and A[16] takes a staggering 1899335 rewrites. The 
-- upshot is that even an access control system which is perfectly empty 
-- apart from 16 teams containing one user each is too large to model. 

-- It would seem to me that whenever there is synchronization involved
-- in object composition this algorithmic problem will arise. For example
-- I would expect the ATM case study to become rapidly unusable in the
-- same way (although I haven't tested it). 

-- The actual output:

-- Date: Tue Mar 31 10:41:26 MET DST 1998
-- System:            -- CafeOBJ system Version 1.4.0(Beta-5) --
--                 built: 1998 Mar 19 Thu 9:24:55 GMT
--                       prelude file: std.bin
-- Apologies: for the ^M characters at the end of every line of
-- CafeOBJ output. It's something to do with emacs and telnet,
-- and has no bearing on the CafeOBJ computations.

-- NAT> in acc6
-- in acc6
-- -- processing input : ./acc6.mod
-- -- defining module! PROJECTID
-- [Warning]: redefining module PROJECTID ..._* done.
-- -- defining module! ROLEID
-- [Warning]: redefining module ROLEID ..._* done.
-- -- defining module! TEAMID
-- [Warning]: redefining module TEAMID ..._* done.
-- -- defining module! MODULEID
-- [Warning]: redefining module MODULEID ..._* done.
-- -- defining module! TOOLID
-- [Warning]: redefining module TOOLID ..._* done.
-- -- defining module! USERID
-- [Warning]: redefining module USERID _*...._* done.
-- -- defining module* USER
-- [Warning]: redefining module USER ...._* done.
-- -- defining module* PROJECT
-- [Warning]: redefining module PROJECT ._*......._....*
-- ** system already proved =*= is a congruence of PROJECT done.
-- -- defining module* PROJECTS
-- [Warning]: redefining module PROJECTS _*_*.........._....*
-- ** system failed to prove =*= is a congruence of PROJECTS done.
-- -- defining module* COMMUNICATION-CHANNEL
-- [Warning]: redefining module COMMUNICATION-CHANNEL ._* done.
-- -- defining module! FRAMEWORK-RESOURCE
-- [Warning]: redefining module FRAMEWORK-RESOURCE ............._* done.
-- -- defining module! ACCESS-TYPE
-- [Warning]: redefining module ACCESS-TYPE ............_* done.
-- -- defining module! PROJECT-RESOURCE
-- [Warning]: redefining module PROJECT-RESOURCE _*......._..* done.
-- -- defining module! FRAMEWORK-PRIVILEGE
-- [Warning]: redefining module FRAMEWORK-PRIVILEGE ._*......._...* done.
-- -- defining module! PROJECT-PRIVILEGE
-- [Warning]: redefining module PROJECT-PRIVILEGE ._*......._...* done.
-- -- defining module* TEAM
-- [Warning]: redefining module TEAM ............._................*
-- ** system failed to prove =*= is a congruence of TEAM done.
-- -- defining module* ROLE
-- [Warning]: redefining module ROLE ._*..............._.....................*
-- ** system already proved =*= is a congruence of ROLE done.
-- -- defining module* TEAMS
-- [Warning]: redefining module TEAMS ............_.......*
-- ** system failed to prove =*= is a congruence of TEAMS done.
-- -- defining module* ROLES
-- [Warning]: redefining module ROLES ..............._..............*
-- ** system failed to prove =*= is a congruence of ROLES done.
-- -- defining module* PERMISSIONS
-- [Warning]: redefining module PERMISSIONS _*_*.,,,,,,_,,*_*..............................._............................................................................*
-- ** system failed to prove =*= is a congruence of PERMISSIONS done.
-- -- defining module* ACCESS-CONTROL
-- [Warning]: redefining module ACCESS-CONTROL _*_*..,,,,,,,,_,,*,,,,,_,,*,,,,,_,,*..........................._..................*
-- ** system failed to prove =*= is a congruence of ACCESS-CONTROL done.

-- NAT> in testacc.mod
-- in testacc.mod
-- -- processing input : /users1/hbh/CAFEOBJ/nelsis/testacc.mod
-- -- defining module! LIST-INT
-- [Warning]: redefining module LIST-INT ........_..* done.
-- -- defining module* TEST-ACCESS-CONTROL
-- [Warning]: redefining module TEST-ACCESS-CONTROL _*_*.,,,,,,,,,_,,*,,,,,_,,*,,,,,_,,*,,,,,_,,*_*........._....* done.

-- NAT> in input1
-- in input1
-- -- processing input : ./input1.mod
-- -- opening module TEST-ACCESS-CONTROL(P).
-- [Warning]: another module already open: ROLE
--            closing this module...
--            . done._*
-- -- reduce in %(P.TEST-ACCESS-CONTROL) : U [ 1 ] has-access-to < team 
--     , modify > given perms A [ 1 ]
-- false : Bool
-- (0.010 sec for parse, 60 rewrites(0.010 sec), 211 match attempts)
-- -- reduce in %(P.TEST-ACCESS-CONTROL) : U [ 0 ] has-access-to < team 
--     , modify > given perms A [ 1 ]
-- true : Bool
-- (0.010 sec for parse, 63 rewrites(0.010 sec), 218 match attempts)
-- -- reduce in %(P.TEST-ACCESS-CONTROL) : U [ 54 ] is-member-of initial-team-name
--      U [ 0 ] given A [ 8 ]
-- false : Bool
-- (0.000 sec for parse, 7401 rewrites(1.450 sec), 19390 match attempts)
-- -- reduce in %(P.TEST-ACCESS-CONTROL) : U [ 1 ] is-member-of initial-team-name
--      U [ 0 ] given A [ 0 , L2 , 1 ]
-- true : Bool
-- (0.000 sec for parse, 99 rewrites(0.020 sec), 320 match attempts)
-- -- reduce in %(P.TEST-ACCESS-CONTROL) : U [ 2 ] is-member-of initial-team-name
--      U [ 0 ] given A [ 0 , L3 , 1 ]
-- true : Bool
-- (0.010 sec for parse, 215 rewrites(0.050 sec), 760 match attempts)
-- -- reduce in %(P.TEST-ACCESS-CONTROL) : U [ 2 ] is-member-of initial-team-name
--      U [ 0 ] given A [ 0 , L3 , 2 ]
-- true : Bool
-- (0.010 sec for parse, 624 rewrites(0.100 sec), 2073 match attempts)
-- -- reduce in %(P.TEST-ACCESS-CONTROL) : "Framework Manager" has-access-to
--      < role , create > given init-acc-sys
-- false : Bool
-- (0.010 sec for parse, 3 rewrites(0.000 sec), 19 match attempts)

-- %TEST-ACCESS-CONTROL(P)> red perms A[2] .
-- red perms A[2] .
-- [Warning]: reduction of hidden-sorted term is meaningless!
-- -- reduce in %(P.TEST-ACCESS-CONTROL) : perms A [ 2 ]
-- add-perm(initial-team-name U [ 1 ],U [ 1 ],"Team Manager",add-team(
--   U [ 1 ],add-perm(initial-team-name U [ 0 ],U [ 0 ],"Team Manager",
--   add-team(U [ 0 ],init-permissions)))) : Permissions
-- (0.000 sec for parse, 55 rewrites(0.010 sec), 130 match attempts)

-- %TEST-ACCESS-CONTROL(P)> red perms A[4] .
-- red perms A[4] .
-- [Warning]: reduction of hidden-sorted term is meaningless!
-- -- reduce in %(P.TEST-ACCESS-CONTROL) : perms A [ 4 ]
-- add-perm(initial-team-name U [ 3 ],U [ 3 ],"Team Manager",add-team(
--   U [ 3 ],add-perm(initial-team-name U [ 2 ],U [ 2 ],"Team Manager",
--   add-team(U [ 2 ],add-perm(initial-team-name U [ 1 ],U [ 1 ],"Team Manager",
--   add-team(U [ 1 ],add-perm(initial-team-name U [ 0 ],U [ 0 ],"Team Manager",
--   add-team(U [ 0 ],init-permissions)))))))) : Permissions
-- (0.000 sec for parse, 335 rewrites(0.050 sec), 874 match attempts)

-- %TEST-ACCESS-CONTROL(P)> red perms A[8] .
-- red perms A[8] .
-- [Warning]: reduction of hidden-sorted term is meaningless!
-- -- reduce in %(P.TEST-ACCESS-CONTROL) : perms A [ 8 ]
-- add-perm(initial-team-name U [ 7 ],U [ 7 ],"Team Manager",add-team(
--   U [ 7 ],add-perm(initial-team-name U [ 6 ],U [ 6 ],"Team Manager",
--   add-team(U [ 6 ],add-perm(initial-team-name U [ 5 ],U [ 5 ],"Team Manager",
--   add-team(U [ 5 ],add-perm(initial-team-name U [ 4 ],U [ 4 ],"Team Manager",
--   add-team(U [ 4 ],add-perm(initial-team-name U [ 3 ],U [ 3 ],"Team Manager",
--   add-team(U [ 3 ],add-perm(initial-team-name U [ 2 ],U [ 2 ],"Team Manager",
--   add-team(U [ 2 ],add-perm(initial-team-name U [ 1 ],U [ 1 ],"Team Manager",
--   add-team(U [ 1 ],add-perm(initial-team-name U [ 0 ],U [ 0 ],"Team Manager",
--   add-team(U [ 0 ],init-permissions)))))))))))))))) : Permissions
-- (0.000 sec for parse, 7063 rewrites(1.660 sec), 18586 match attempts)

-- %TEST-ACCESS-CONTROL(P)> red perms A[16] .
-- red perms A[16] .
-- [Warning]: reduction of hidden-sorted term is meaningless!
-- -- reduce in %(P.TEST-ACCESS-CONTROL) : perms A [ 16 ]
-- add-perm(initial-team-name U [ 15 ],U [ 15 ],"Team Manager",add-team(
--   U [ 15 ],add-perm(initial-team-name U [ 14 ],U [ 14 ],"Team Manager",
--   add-team(U [ 14 ],add-perm(initial-team-name U [ 13 ],U [ 13 ],
--   "Team Manager",add-team(U [ 13 ],add-perm(initial-team-name U [
--    12 ],U [ 12 ],"Team Manager",add-team(U [ 12 ],add-perm(initial-team-name
--    U [ 11 ],U [ 11 ],"Team Manager",add-team(U [ 11 ],add-perm(initial-team-name
--    U [ 10 ],U [ 10 ],"Team Manager",add-team(U [ 10 ],add-perm(initial-team-name
--    U [ 9 ],U [ 9 ],"Team Manager",add-team(U [ 9 ],add-perm(initial-team-name
--    U [ 8 ],U [ 8 ],"Team Manager",add-team(U [ 8 ],add-perm(initial-team-name
--    U [ 7 ],U [ 7 ],"Team Manager",add-team(U [ 7 ],add-perm(initial-team-name
--    U [ 6 ],U [ 6 ],"Team Manager",add-team(U [ 6 ],add-perm(initial-team-name
--    U [ 5 ],U [ 5 ],"Team Manager",add-team(U [ 5 ],add-perm(initial-team-name
--    U [ 4 ],U [ 4 ],"Team Manager",add-team(U [ 4 ],add-perm(initial-team-name
--    U [ 3 ],U [ 3 ],"Team Manager",add-team(U [ 3 ],add-perm(initial-team-name
--    U [ 2 ],U [ 2 ],"Team Manager",add-team(U [ 2 ],add-perm(initial-team-name
--    U [ 1 ],U [ 1 ],"Team Manager",add-team(U [ 1 ],add-perm(initial-team-name
--    U [ 0 ],U [ 0 ],"Team Manager",add-team(U [ 0 ],init-permissions)
--   ))))))))))))))))))))))))))))))) : Permissions
-- (0.000 sec for parse, 1899335 rewrites(417.010 sec), 4978042 match attempts)

-- %TEST-ACCESS-CONTROL(P)> 


-- 	---------------------------------------------------
-- acc6.mod contains:

-- Specification of Nelsis 

mod! PROJECTID {
  protecting (QID)
  [ Id < ProjectId ]
  op no-projectid : -> ProjectId	-- error
}

mod! ROLEID {
  protecting (QID)
  [ Id < RoleId ]
  op no-roleid : -> RoleId		-- error
}

mod! TEAMID {
  protecting (QID)
  [ Id < TeamId ]
  op no-teamid : -> TeamId		-- error
}

mod! MODULEID {
  protecting (QID)
  [ Id < ModuleId ]
  op no-moduleid : -> ModuleId		-- error
}

mod! TOOLID {
  protecting (QID)
  [ Id < ToolId ]
  op no-toolid : -> ToolId		-- error
}

mod! USERID {
  protecting (QID + TEAMID)
  [ Id < UserId ]
  op no-userid : -> UserId		-- error
  op initial-team-name_ : UserId -> TeamId
}

-- Specification of access control 

mod* USER {
  protecting (TEAMID)
  [ User ]
  op no-user : -> User
  op initial-team-name_ : User -> TeamId
}

mod* PROJECT {
  *[ Project ]*
  protecting (PROJECTID + USERID)
  op init-project : UserId ProjectId -> Project		-- initial state
  op no-project : -> Project				-- error
  bop project-name_ : Project -> ProjectId 		-- attribute
  bop project-manager_ : Project -> UserId		-- attribute

  var Uid : UserId 
  var Pid : ProjectId
  eq project-manager (init-project (Uid, Pid)) = Uid .
  eq project-manager no-project = no-userid .

  eq project-name (init-project (Uid, Pid)) = Pid .
  eq project-name no-project = no-projectid .
}

mod* PROJECTS (P :: PROJECT) {
  *[ Projects ]*
  op make-project : UserId ProjectId Projects -> Projects	
							-- method
  op init-projects : -> Projects			-- initial state
  bop project : ProjectId Projects -> Project		-- projection
  pred _exists-in_ : ProjectId Projects			-- attribute
  bop project-manager : ProjectId Projects -> UserId	-- attribute
 
  var Uid : UserId 
  vars Pid Pid' : ProjectId
  var Ps : Projects
  eq project (Pid, init-projects) = no-project .
  eq project (Pid, make-project (Uid, Pid', Ps)) = 
			if ((Pid == Pid') and not (Pid' exists-in Ps))
			then init-project (Uid, Pid)
			else project (Pid, Ps) fi .
  eq Pid exists-in Ps = project (Pid, Ps) =/= no-project .
  eq project-manager (Pid, Ps) = project-manager (project (Pid, Ps)) .
}

mod* COMMUNICATION-CHANNEL {
  [ CommChnl ]
}

mod! FRAMEWORK-RESOURCE {
  [ FrameworkResource ]
  ops role team project project-privilege do not-my-do designer metadata
	framework-privilege flowgraph role-creation role-deletion 
						: -> FrameworkResource
}

mod! ACCESS-TYPE {
  [ AccessType ]
  ops create modify delete execute open write read assign-to-role
	delete-role assign-to-designer assign-to-team : -> AccessType
}

mod! PROJECT-RESOURCE {
  protecting (MODULEID + TOOLID)
  [ ModuleId ToolId < ProjectResource ]
  pred _is-module-name : ProjectResource
  pred _is-tool-name : ProjectResource
  op role-in-project : -> ProjectResource 

  var mid : ModuleId
  var tid : ToolId
  eq mid is-module-name = true .
  eq tid is-tool-name = true .
}

mod! FRAMEWORK-PRIVILEGE {
  [ FrameworkPrivilege < FrameworkPrivilege? ]
  protecting (FRAMEWORK-RESOURCE + ACCESS-TYPE) 
  pred (_ is FrameworkPrivilege) : FrameworkPrivilege?
  op <_,_> : FrameworkResource AccessType -> FrameworkPrivilege?
  op resource_ : FrameworkPrivilege? -> FrameworkResource
  op access-type_ : FrameworkPrivilege? -> AccessType
  
  var fr : FrameworkResource
  var ac : AccessType
  eq resource < fr, ac > = fr .
  eq access-type < fr , ac > = ac .
  eq (< fr , ac >) is FrameworkPrivilege = 
		((fr == role) and 
				(ac == create or 
				 ac == modify or 
				 ac == delete or 
				 ac == assign-to-designer or
				 ac == assign-to-team
         			)
		) or
		((fr == team) and 
				(ac == create or 
				 ac == modify or 
				 ac == delete or
				 ac == delete-role
				)
		) or 
		((fr == project) and 
				(ac == modify or
				 ac == delete or 
				 ac == execute or 
				 ac == write or 
				 ac == read
				)
	        ) or 
		((fr == project-privilege) and 
				(ac == assign-to-role or
				 ac == create
				)
		) or
		((fr == framework-privilege) and 
				(ac == assign-to-role or
				 ac == create
				)
		) or 
		((fr == metadata) and 
				(ac == read)
		) or 
		((fr == flowgraph) and 
				(ac == create or 
				 ac == modify or 
				 ac == delete or 
				 ac == execute or 
				 ac == open
				)
		) .
}

mod! PROJECT-PRIVILEGE {
  [ ProjectPrivilege < ProjectPrivilege? ]
  protecting (PROJECT-RESOURCE + ACCESS-TYPE)
  pred (_ is ProjectPrivilege) : ProjectPrivilege?
  op <_,_> : ProjectResource AccessType -> ProjectPrivilege?
  op resource_ : ProjectPrivilege? -> ProjectResource
  op access-type_ : ProjectPrivilege? -> AccessType

  var Pr : ProjectResource
  var Ac : AccessType
  eq resource < Pr, Ac > = Pr .
  eq access-type < Pr , Ac > = Ac .
  eq (< Pr , Ac >) is ProjectPrivilege = 
		((Pr is-module-name) and (Ac == create or
					  Ac == modify or
				  	  Ac == delete or
				  	  Ac == read
					 )
		) or
		((Pr is-tool-name) and (Ac == execute)
 		) or 
		((Pr == role-in-project and Ac == assign-to-team)
		) .
}

mod* TEAM {
  *[ Team ]*
  protecting (USERID)
  op init-team_ : UserId -> Team			-- initial state
  op no-team : -> Team					-- error

  bop team-manager_ : Team -> UserId			-- projection
  bop teamname_ : Team -> TeamId			-- attribute
  pred _is-member-of_ : UserId Team 

  bop add-user : UserId Team -> Team 			-- method 
							-- (constructor)
  bop delete-user : UserId Team -> Team 		-- method

  bop _adds-user_to_ : UserId UserId Team -> Team	  	-- defined method
  bop _deletes-user_from_ : UserId UserId Team -> Team 	-- defined method 

  vars Uid Vid : UserId 
  var T : Team

  eq add-user (Uid, no-team) = no-team .

  eq team-manager no-team = no-userid .
  eq team-manager (init-team Uid) = Uid .
  eq team-manager add-user (Uid, T) = team-manager T .

  eq teamname no-team = no-teamid .
  eq teamname (init-team Uid) = initial-team-name Uid .
  eq teamname add-user (Uid, T) = teamname T .

  eq Uid is-member-of no-team = false .
  eq Uid is-member-of (init-team Vid) = Uid == Vid .
  eq Uid is-member-of (add-user (Vid, T)) = if Uid == Vid then true else
						Uid is-member-of T fi .

  cq Uid adds-user Vid to T = T if team-manager T =/= Uid 
			or (Vid is-member-of T) . 
  cq Uid adds-user Vid to T = add-user (Vid, T) 
		if team-manager T == Uid and not (Vid is-member-of T) .

  cq Uid deletes-user Vid from T = T if team-manager T =/= Uid or 
			team-manager T == Vid or not (Vid is-member-of T) .
  cq Uid deletes-user Vid from T = delete-user (Vid, T) 
		if team-manager T == Uid and 
		   team-manager T =/= Vid and (Vid is-member-of T) .

  eq delete-user (Vid, no-team) = no-team .
  eq delete-user (Vid, (add-user (Uid, T))) = if Vid == Uid then T else 
				add-user (Uid, (delete-user (Vid, T))) fi .
}  

mod* ROLE {
  *[ Role ]*
  protecting (FRAMEWORK-PRIVILEGE + PROJECT-PRIVILEGE + ROLEID)
  op init-role_ : RoleId -> Role			-- initial state
  op no-role : -> Role
  ops framework-manager project-manager team-manager : -> Role
  bop add-framework-privilege : FrameworkPrivilege? Role -> Role
							-- method
  bop add-project-privilege : ProjectPrivilege? Role -> Role
							-- method
  bop name_ : Role -> RoleId 				-- attribute
  pred _has-framework-privilege_ : Role FrameworkPrivilege?
  pred _has-project-privilege_ : Role ProjectPrivilege?
  
  vars Fr Fr' : FrameworkPrivilege?
  vars Pr Pr' : ProjectPrivilege?
  var R : Role
  var Rid : RoleId 

  eq name (init-role Rid) = Rid .
  eq name no-role = no-roleid .
  eq name framework-manager = 'Framework_Manager .
  eq name project-manager = 'Project_Manager .
  eq name team-manager = 'Team_Manager .
  eq name (add-framework-privilege (Fr, R)) = name R .
  eq name (add-project-privilege (Pr, R)) = name R .

  eq (init-role Rid) has-framework-privilege Fr = false .
  eq no-role has-framework-privilege Fr = false .
  eq framework-manager has-framework-privilege Fr = 
			(Fr == < role ,	create >) 
			or (Fr == < role , delete >) 
			or (Fr == < role , modify >) 
			or (Fr == < role-creation , assign-to-designer >)
			or (Fr == < role-deletion , assign-to-designer >) . 
  eq project-manager has-framework-privilege Fr = 
			(Fr == < team , assign-to-role >) 
			or (Fr == < team , delete-role >) 
			or (Fr == < project-privilege , assign-to-role >)
			or (Fr == < project , delete >) .
  eq team-manager has-framework-privilege Fr = 
			(Fr == < designer , assign-to-role >) 
			or (Fr == < designer , delete-role >) 
			or (Fr == < team , modify >) 
			or (Fr == < team , delete >) .
  eq add-framework-privilege (Fr, R) has-framework-privilege Fr' = if
	(Fr == Fr') then true else R has-framework-privilege Fr' fi .
  eq add-project-privilege (Pr, R) has-framework-privilege Fr = 
					R has-framework-privilege Fr .

  eq (init-role Rid) has-project-privilege Pr = false .
  eq no-role has-project-privilege Pr = false .
  eq framework-manager has-project-privilege Pr = false .
  eq project-manager has-project-privilege Pr = 
			(Pr == < role-in-project , assign-to-team >) .
  eq team-manager has-project-privilege Pr = false .
  eq add-framework-privilege (Fr, R) has-project-privilege Pr = 
					R has-project-privilege Pr .
  eq add-project-privilege (Pr, R) has-project-privilege Pr' = if
 	(Pr == Pr') then true else R has-project-privilege Pr' fi .
}

mod* TEAMS {
  *[ Teams ]*
  protecting (TEAM)
  op init-teams : -> Teams			-- initial state
  bop new-team : UserId Teams -> Teams		-- method
  bop add-user : UserId TeamId Teams -> Teams	-- method
  bop delete-user : UserId TeamId Teams -> Teams 
						-- method
  bop team : TeamId Teams -> Team		-- projection  
  pred _exists-in_ : TeamId Teams		-- attribute
  bop team-manager : TeamId Teams -> UserId	-- attribute

  vars Tid Tid' : TeamId
  var Ts : Teams
  var Uid : UserId
  cq new-team (Uid, Ts) = Ts if (teamname (init-team Uid)) exists-in Ts .
  eq team (Tid, init-teams) = no-team .
  eq team (Tid, (new-team (Uid, Ts))) = if (Tid == teamname (init-team
		Uid)) then (init-team Uid) else team (Tid, Ts) fi . 
  eq team (Tid, add-user (Uid, Tid', Ts)) = 
		if (Tid == Tid')
		then add-user (Uid, (team (Tid, Ts)))
		else team (Tid, Ts) fi .
  eq team (Tid, delete-user (Uid, Tid', Ts)) = 
		if (Tid == Tid')
		then delete-user (Uid, (team (Tid, Ts)))
		else team (Tid, Ts) fi .

  eq Tid exists-in Ts = team (Tid, Ts) =/= no-team .
  eq team-manager (Tid, Ts) = team-manager (team (Tid, Ts)) .
}

mod* ROLES {
  *[ Roles ]*
  protecting (ROLE)
  op init-roles : -> Roles				-- initial state
  bop add-role : RoleId Roles -> Roles			-- method
  bop add-framework-privilege : FrameworkPrivilege? RoleId Roles
				-> Roles		-- method
  bop add-project-privilege : ProjectPrivilege? RoleId Roles
				-> Roles		-- method
  bop role : RoleId Roles -> Role			-- projection
  bop framework-manager_ : Roles -> Role		
  bop project-manager_ : Roles -> Role 			 
  bop team-manager_ : Roles -> Role			
  bop _exists-in_ : RoleId Roles -> Bool		-- attribute 
 
  vars Rid Rid' : RoleId 
  var Pp : ProjectPrivilege?
  var Rs : Roles
  var Fp : FrameworkPrivilege?
  eq role ('Framework_Manager, init-roles) = framework-manager .
  eq role ('Project_Manager, init-roles) = project-manager .
  eq role ('Team_Manager, init-roles) = team-manager .
  cq role (Rid, init-roles) = no-role if (Rid =/= 'Framework_Manager) and
					(Rid =/= 'Project_Manager) and
					(Rid =/= 'Team_Manager) .
  eq role (Rid, (add-role (Rid', Rs))) = if (Rid == Rid') then 
	(init-role Rid) else role (Rid', Rs) fi .
  eq role (Rid, (add-framework-privilege (Fp, Rid', Rs))) = 
		add-framework-privilege (Fp, (role (Rid, Rs))) .
  eq role (Rid, (add-project-privilege (Pp, Rid', Rs))) = 
		add-project-privilege (Pp, (role (Rid, Rs))) .

  eq framework-manager init-roles = framework-manager .
  eq framework-manager (add-role (Rid, Rs)) = framework-manager Rs .
  
  eq project-manager init-roles = project-manager .
  eq project-manager (add-role (Rid, Rs)) = project-manager Rs .

  eq team-manager init-roles = team-manager .
  eq team-manager (add-role (Rid, Rs)) = team-manager Rs .

  eq Rid exists-in Rs = role (Rid, Rs) =/= no-role .
}

mod* PERMISSIONS (P :: PROJECT) {
  protecting (ROLES + TEAMS + PROJECTS(P))
  *[ Permissions ]*
  op init-permissions : -> Permissions			-- initial state
  bop roles_ : Permissions -> Roles			-- projection
  bop teams_ : Permissions -> Teams	 		-- projection
  bop projects_ : Permissions -> Projects		-- projection

  bop add-role : RoleId Permissions -> Permissions	-- method
  bop add-team : UserId Permissions -> Permissions 	-- method
  bop add-perm : TeamId UserId RoleId Permissions -> Permissions
							-- method
  bop add-project-partner : TeamId RoleId ProjectId Permissions ->
					Permissions	-- method
  bop add-framework-privilege : FrameworkPrivilege? RoleId Permissions ->  
					Permissions	-- method
  bop add-project-privilege : ProjectPrivilege? RoleId Permissions -> 
					Permissions	-- method
  bop make-project : UserId ProjectId Permissions -> Permissions	
							-- method
  bop add-user : UserId TeamId Permissions -> Permissions
							-- method
  bop delete-user : UserId TeamId Permissions -> Permissions
							-- method 
  pred _plays-role_in-team_given_ : UserId RoleId TeamId Permissions 
							-- attribute
  pred _plays-role_in-project_given_ : TeamId RoleId ProjectId Permissions 
							-- attribute
  pred _has-access-to_in_given_ : UserId ProjectPrivilege? ProjectId 
					Permissions 	-- attribute
  pred _has-access-to_given_ : UserId FrameworkPrivilege? Permissions
							-- attribute
  pred team_exists-in_ : TeamId Permissions		-- attribute
  pred role_exists-in_ : RoleId Permissions		-- attribute
  pred project_exists-in_ : ProjectId Permissions	-- attribute
  bop project-manager : ProjectId Permissions -> UserId	-- attribute
  bop team-manager : TeamId Permissions -> UserId	-- attribute

  var Pm : Permissions
  vars Uid Uid' Vid : UserId
  vars Tid Tid' : TeamId
  vars Rid Rid' : RoleId
  vars Pid Pid' : ProjectId
  var Fp : FrameworkPrivilege?
  var Pp : ProjectPrivilege?

  eq roles init-permissions = init-roles . 
  eq roles (add-role (Rid, Pm)) = add-role (Rid, roles Pm) .
  eq roles (add-perm (Tid, Vid, Rid, Pm)) = roles Pm .
  eq roles (add-team (Uid, Pm)) = roles Pm .
  eq roles (add-project-partner (Tid, Rid, Pid, Pm)) = roles Pm .
  eq roles (add-framework-privilege (Fp, Rid, Pm)) = 
	add-framework-privilege (Fp, Rid, roles Pm) .
  eq roles (add-project-privilege (Pp, Rid, Pm)) = 
	add-project-privilege (Pp, Rid, roles Pm) .
  eq roles make-project (Uid, Pid, Pm) = roles Pm .
  eq roles (add-user (Uid, Tid, Pm)) = roles Pm .
  eq roles (delete-user (Uid, Tid, Pm)) = roles Pm .

  eq teams init-permissions = init-teams . 
  eq teams (add-role (Rid, Pm)) = teams Pm .
  eq teams (add-perm (Tid, Vid, Rid, Pm)) = teams Pm .
  eq teams (add-team (Uid, Pm)) = new-team (Uid, teams Pm) .
  eq teams (add-project-partner (Tid, Rid, Pid, Pm)) = teams Pm .
  eq teams (add-framework-privilege (Fp, Rid, Pm)) = teams Pm .
  eq teams (add-project-privilege (Pp, Rid, Pm)) = teams Pm .
  eq teams make-project (Uid, Pid, Pm) = teams Pm .
  eq teams (add-user (Uid, Tid, Pm)) = add-user (Uid, Tid, teams Pm) .
  eq teams (delete-user (Uid, Tid, Pm)) = delete-user (Uid, Tid, teams Pm) . 

  eq projects init-permissions = init-projects . 
  eq projects (add-role (Rid, Pm)) = projects Pm .
  eq projects (add-perm (Tid, Vid, Rid, Pm)) = projects Pm .
  eq projects (add-team (Uid, Pm)) = projects Pm .
  eq projects (add-project-partner (Tid, Rid, Pid, Pm)) = projects Pm .
  eq projects (add-framework-privilege (Fp, Rid, Pm)) = projects Pm .
  eq projects (add-project-privilege (Pp, Rid, Pm)) = projects Pm .
  eq projects make-project (Uid, Pid, Pm) = 
				make-project (Uid, Pid, projects Pm) . 
  eq projects (add-user (Uid, Tid, Pm)) = projects Pm .
  eq projects (delete-user (Uid, Tid, Pm)) = projects Pm .

  eq Uid plays-role Rid in-team Tid given init-permissions = false .
  eq Uid plays-role Rid in-team Tid given (add-role (Rid', Pm)) = 
		Uid plays-role Rid in-team Tid given Pm .
  eq Uid plays-role Rid in-team Tid given (add-team (Uid', Pm)) = 
		Uid plays-role Rid in-team Tid given Pm .
  eq Uid plays-role Rid in-team Tid given (add-perm (Tid', Vid, Rid', Pm)) =  
		((Uid == Vid) and (Tid == Tid') and (Rid == Rid') and
		(Tid exists-in (teams Pm)) and (Rid exists-in (roles Pm)))
	or	(Uid plays-role Rid in-team Tid given Pm) . 
  eq Uid plays-role Rid in-team Tid 
			given (add-project-partner (Tid', Rid', Pid, Pm)) = 
			Uid plays-role Rid in-team Tid given Pm . 
  eq Uid plays-role Rid in-team Tid given 
			add-framework-privilege (Fp, Rid', Pm) = 	
		Uid plays-role Rid in-team Tid given Pm .
  eq Uid plays-role Rid in-team Tid given 
			add-project-privilege (Pp, Rid', Pm) = 	
		Uid plays-role Rid in-team Tid given Pm .
  eq Uid plays-role Rid in-team Tid given make-project (Vid, Pid, Pm) = 
		if ((Uid == Vid) and (Rid == 'Project_Manager) and 
		    (Uid is-member-of (team (Tid, (teams Pm)))))
		then true
		else Uid plays-role Rid in-team Tid given Pm fi .   
  eq Uid plays-role Rid in-team Tid given add-user (Uid', Tid', Pm) = 	
		Uid plays-role Rid in-team Tid given Pm .
  eq Uid plays-role Rid in-team Tid given delete-user (Uid', Tid', Pm) =
		Uid plays-role Rid in-team Tid given Pm .

  eq Tid plays-role Rid in-project Pid given init-permissions = false .
  eq Tid plays-role Rid in-project Pid given (add-role (Rid', Pm)) =
		  Tid plays-role Rid in-project Pid given Pm .
  eq Tid plays-role Rid in-project Pid given (add-team (Uid', Pm)) =
		  Tid plays-role Rid in-project Pid given Pm .
  eq Tid plays-role Rid in-project Pid 
			given (add-perm (Tid', Uid, Rid', Pm)) =   
			Tid plays-role Rid in-project Pid given Pm .
  eq Tid plays-role Rid in-project Pid given 
		(add-project-partner (Tid', Rid', Pid', Pm)) = 
		((Tid == Tid') and (Rid == Rid') and (Pid == Pid') and
		(Tid exists-in (teams Pm)) and (Rid exists-in (roles Pm)) 
  		and (Pid exists-in (projects Pm)))
	or	Tid plays-role Rid in-project Pid given Pm . 
  eq Tid plays-role Rid in-project Pid given 
			add-framework-privilege (Fp, Rid', Pm) = 
		  Tid plays-role Rid in-project Pid given Pm .
  eq Tid plays-role Rid in-project Pid given 
			add-project-privilege (Pp, Rid', Pm) = 
		  Tid plays-role Rid in-project Pid given Pm .
  eq Tid plays-role Rid in-project Pid given make-project (Vid, Pid, Pm) =  
		  Tid plays-role Rid in-project Pid given Pm .
  eq Tid plays-role Rid in-project Pid given add-user (Uid', Tid', Pm) =  
		  Tid plays-role Rid in-project Pid given Pm .
  eq Tid plays-role Rid in-project Pid given delete-user (Uid', Tid', Pm) =
		  Tid plays-role Rid in-project Pid given Pm .

  eq Uid has-access-to Pp in Pid given init-permissions = false .
  eq Uid has-access-to Pp in Pid given add-role (Rid', Pm) = 
		Uid has-access-to Pp in Pid given Pm .
  eq Uid has-access-to Pp in Pid given add-team (Uid', Pm) = 
		Uid has-access-to Pp in Pid given Pm .
  eq Uid has-access-to Pp in Pid given (add-perm (Tid, Vid, Rid, Pm)) = 
		if ((Uid == Vid) and 
		    (role (Rid, (roles Pm)) has-project-privilege Pp))
		then (Tid plays-role Rid in-project Pid 
			given add-perm (Tid, Vid, Rid, Pm)
			or
		      Uid has-access-to Pp in Pid given Pm)
		else Uid has-access-to Pp in Pid given Pm fi .
  eq Uid has-access-to Pp in Pid 
			given (add-project-partner (Tid, Rid, Pid', Pm)) =  
		if ((Pid == Pid') and
		    (Pid exists-in (projects Pm)) and 
		    (role (Rid, (roles Pm)) has-project-privilege Pp))
		then (Uid plays-role Rid in-team Tid given Pm
			or
		      Uid has-access-to Pp in Pid given Pm)
		else Uid has-access-to Pp in Pid given Pm fi .
  eq Uid has-access-to Pp in Pid given
			add-framework-privilege (Fp, Rid', Pm) = 
			Uid has-access-to Pp in Pid given Pm .
  eq Uid has-access-to Pp in Pid given 
			add-project-privilege (Pp, Rid', Pm) = 
			Uid has-access-to Pp in Pid given Pm .
  eq Uid has-access-to Pp in Pid given make-project (Vid, Pid, Pm) = 
			Uid has-access-to Pp in Pid given Pm .
  eq Uid has-access-to Pp in Pid given add-user (Uid', Tid', Pm) = 
		Uid has-access-to Pp in Pid given Pm .
  eq Uid has-access-to Pp in Pid given delete-user (Uid', Tid', Pm) = 
		Uid has-access-to Pp in Pid given Pm .
 
  eq Uid has-access-to Fp given init-permissions = false .
  eq Uid has-access-to Fp given add-role (Rid', Pm) = 
		Uid has-access-to Fp given Pm .
  eq Uid has-access-to Fp given add-team (Uid', Pm) = 
		Uid has-access-to Fp given Pm .
  eq Uid has-access-to Fp given (add-perm (Tid, Vid, Rid, Pm)) =
		if ((role (Rid, roles Pm)) has-framework-privilege Fp) 
		then (Uid plays-role Rid in-team Tid 
			given add-perm (Tid, Vid, Rid, Pm) 
			or
		     Uid has-access-to Fp given Pm)
		else Uid has-access-to Fp given Pm fi .
  eq Uid has-access-to Fp given (add-project-partner (Tid, Rid, Pid', Pm)) =  
			Uid has-access-to Fp given Pm . 
  eq Uid has-access-to Fp given add-framework-privilege (Fp, Rid', Pm) = 
			Uid has-access-to Fp given Pm .
  eq Uid has-access-to Fp given add-project-privilege (Pp, Rid', Pm) = 
			Uid has-access-to Fp given Pm .
  eq Uid has-access-to Fp given make-project (Vid, Pid, Pm) = 
			Uid has-access-to Fp given Pm .
  eq Uid has-access-to Fp given add-user (Uid', Tid', Pm) = 
		Uid has-access-to Fp given Pm .
  eq Uid has-access-to Fp given delete-user (Uid', Tid', Pm) = 
		Uid has-access-to Fp given Pm .

  eq team Tid exists-in Pm = Tid exists-in (teams Pm) .
  eq role Rid exists-in Pm = Rid exists-in (roles Pm) .
  eq project Pid exists-in Pm = Pid exists-in (projects Pm) .
  eq project-manager (Pid, Pm) = project-manager (Pid, projects Pm) .
  eq team-manager (Tid, Pm) = team-manager (Tid, teams Pm) .

  eq Tid plays-role 'Team_Manager in-project Pid given Pm = false .
}
				
mod* ACCESS-CONTROL (P :: PROJECT) {
  *[ Acc-Sys ]*
  protecting (PERMISSIONS(P))
  op init-acc-sys : -> Acc-Sys			-- initial state 
  bop _adds-role_to_ : UserId RoleId Acc-Sys -> Acc-Sys
						-- method
  bop _adds-perm___to_ : UserId TeamId UserId RoleId Acc-Sys -> Acc-Sys 
						-- method
  bop _adds-project-partner___to_ : UserId TeamId RoleId ProjectId Acc-Sys  
				-> Acc-Sys	-- method
  bop _adds-team-to_ : UserId Acc-Sys -> Acc-Sys	-- method
  bop _adds-framework-privilege_to_in_ : UserId FrameworkPrivilege? RoleId
			Acc-Sys -> Acc-Sys	-- method
  bop _adds-project-privilege_to_in_ : UserId ProjectPrivilege? RoleId
			Acc-Sys -> Acc-Sys	-- method
  bop make-project : UserId ProjectId Acc-Sys -> Acc-Sys
						-- method
  bop _adds-user_to-team_given_ : UserId UserId TeamId Acc-Sys -> Acc-Sys
						-- method
  bop _deletes-user_from-team_given_ : UserId UserId TeamId Acc-Sys 
				-> Acc-Sys 	-- method

  bop perms_ : Acc-Sys -> Permissions { memo }	-- projection

  pred _has-access-to_in_given_ : UserId ProjectPrivilege? ProjectId 
					Acc-Sys 	-- attribute
  pred _has-access-to_given_ : UserId FrameworkPrivilege? Acc-Sys
						 	-- attribute
  pred team_exists-in_ : TeamId Acc-Sys			-- attribute
  pred role_exists-in_ : RoleId Acc-Sys			-- attribute
  pred project_exists-in_ : ProjectId Acc-Sys		-- attribute
  pred _is-member-of_given_ : UserId TeamId Acc-Sys	-- attribute
  bop project-manager : ProjectId Acc-Sys -> UserId	-- attribute
  bop team-manager : TeamId Acc-Sys -> UserId		-- attribute


  vars Uid Vid : UserId 
  var Tid : TeamId
  var Rid : RoleId
  var Pid : ProjectId
  var Fp : FrameworkPrivilege?
  var Pp : ProjectPrivilege?
  var AccSys : Acc-Sys
  
  eq Uid has-access-to Pp in Pid given AccSys = 
		Uid has-access-to Pp in Pid given perms AccSys .
  eq Uid has-access-to Fp given AccSys = 
		Uid has-access-to Fp given perms AccSys .
  eq team Tid exists-in AccSys = team Tid exists-in perms AccSys .
  eq role Rid exists-in AccSys = role Rid exists-in perms AccSys .
  eq project Pid exists-in AccSys = project Pid exists-in perms AccSys .

  eq Uid is-member-of Tid given AccSys = 
		Uid is-member-of (team (Tid, (teams (perms AccSys)))) .

  eq project-manager (Pid, AccSys) = project-manager (Pid, perms AccSys) .
  eq team-manager (Tid, AccSys) = team-manager (Tid, perms AccSys) .

  eq perms init-acc-sys = init-permissions . 
					-- what about frameworkmanager? 
  eq perms (Uid adds-role Rid to AccSys) = 
	if (Uid has-access-to (< role , create >) given perms AccSys)
	    	and not (Rid exists-in roles (perms AccSys))
  	then add-role (Rid, perms AccSys) 
	else perms AccSys fi .
  eq perms (Uid adds-perm Tid Vid Rid to AccSys) = 
	if Uid has-access-to (< role , assign-to-designer >) 
		given perms AccSys 
	then add-perm (Tid, Vid, Rid, perms AccSys)
	else perms AccSys fi .
  eq perms (Uid adds-project-partner Tid Rid Pid to AccSys) = 
	if (Uid has-access-to (< role , assign-to-team >) given perms AccSys)
	   or ((Rid == 'Project_Manager) and 
	       (project-manager (Pid, AccSys) == Uid))
	then add-project-partner (Tid, Rid, Pid, perms AccSys)
	else perms AccSys fi .
  eq perms (Uid adds-team-to AccSys) = 
	if not ((initial-team-name Uid) exists-in teams (perms AccSys))
	then add-perm (initial-team-name Uid, Uid, 'Team_Manager, 
			add-team (Uid, (perms AccSys))) 
	else perms AccSys fi .
  eq perms (Uid adds-framework-privilege Fp to Rid in AccSys) = 
	if Uid has-access-to (< role , modify >)
		given perms AccSys
	then add-framework-privilege (Fp, Rid, (perms AccSys))
	else perms AccSys fi .
  eq perms (Uid adds-project-privilege Pp to Rid in AccSys) = 
	if Uid has-access-to (< role , modify >)
		given perms AccSys
	then add-project-privilege (Pp, Rid, (perms AccSys))
	else perms AccSys fi .
  eq perms make-project (Uid, Pid, AccSys) = 
			make-project (Uid, Pid, perms AccSys) .
  eq perms (Uid adds-user Vid to-team Tid given AccSys) = 
	if Uid has-access-to (< team , modify >) given perms AccSys
	then add-user (Vid, Tid, perms AccSys)
	else perms AccSys fi .
  eq perms (Uid deletes-user Vid from-team Tid given AccSys) = 
	if Uid has-access-to (< team , modify >) given perms AccSys
	then delete-user (Vid, Tid, perms AccSys)
	else perms AccSys fi .
}

-- testacc.mod contains:

mod! LIST-INT {
  protecting(INT)

  [ NList < List ]

  op nil : -> List
  op _._ : Int List -> NList
  op car_ : NList -> Int
  op cdr_ : NList -> List

  var L : List
  var N : Int

  eq car (N . L) = N .
  eq cdr (N . L) = L .
}

mod* TEST-ACCESS-CONTROL (P :: PROJECT) {
  protecting (ACCESS-CONTROL(P) + LIST-INT)
  op U[_] : Int -> UserId 	-- infinite supply of arbitrary users
  op create_singleton-teams : Int -> Acc-Sys
				-- create n teams containing respectively 
				-- users U[0], ..., U[n-1]
  bop _adds-users_to_given_ : UserId List TeamId Acc-Sys -> Acc-Sys

  var N : Int
  var U : UserId
  var Tid : TeamId 
  var L : List 
  var AccSys : Acc-Sys
  eq create 0 singleton-teams = init-acc-sys .
  cq create N singleton-teams = U[ N - 1 ] adds-team-to 
		(create (N - 1) singleton-teams) if N > 0 .

  eq U adds-users nil to Tid given AccSys = AccSys .
  eq U adds-users (N . L) to Tid given AccSys = U adds-users L to Tid 
			given (U adds-user U[N] to-team Tid given AccSys) . 
}

-- input1.mod contains:

open TEST-ACCESS-CONTROL 
  op A[_] : Int -> Acc-Sys .
  op A[_,_,_] : Int List Int -> Acc-Sys .
  ops A1 A2 A3 : -> Acc-Sys .
  ops L1 L2 L3 : -> List .
  op FM1 : -> Acc-Sys .

  vars M N : Int .
  var L : List .
  eq L1 = (2 . 54 . 3 . nil) .
  eq L2 = (1 . nil) .
  eq L3 = (1 . 2 . nil) .
  eq A[N] = create N singleton-teams .
  eq A[M,L,N] = U[M] adds-users L to (initial-team-name U[M]) given A[N] .
  eq FM1 = ('Framework_Manager adds-team-to init-acc-sys) .

-- red U[1] has-access-to < team , modify > given perms A[1] .
-- red U[0] has-access-to < team , modify > given perms A[1] .
-- red U[54] is-member-of (initial-team-name U[0]) given A[8] .
-- red U[1] is-member-of (initial-team-name U[0]) given A[0,L2,1] .
-- red U[2] is-member-of (initial-team-name U[0]) given A[0,L3,1] .
-- red U[2] is-member-of (initial-team-name U[0]) given A[0,L3,2] .
-- red 'Framework_Manager has-access-to < role , create > given init-acc-sys .
eof

