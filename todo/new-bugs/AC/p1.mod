red mpirun(3, 
  if(not(pid = 0)){
    int x ;
    send(pid,0);
    recv(x,0);
  } 
  if(pid = 0){
    int x ; int i ; 
    i := 1 ;
      while (np > i) {
        recv(x,any) ;
        send(x,np - i) ;
        i := i + 1 ;
      }
  } 
) =(*,*)=>! L:List .
