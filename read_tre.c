#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include "forlan.h"

extern FILE * input_file ;
extern FILE * output_file ;
extern FILE * caca_file ;
int goto_read_tree() ;
int read_tree (int  * , int *  ) ;
char buffer [ 80000 ] ;
int ances [ MAXNODES ] ;
int nt, firs [ MAXNODES ], sis  [ MAXNODES ],optlist[ MAXNODES ], nnods, intnods ;
int lefpar= 0 , derpar= 0 , nuters=  0  ;
typedef struct {
     int num_confs ;
     double min_age ;
     double max_age ;
     double min_aln_age ;
     double max_aln_age ;
     double minavage ;
     double maxavage ;
     char * sps_name ;
     int sp_number ;
     int conflist [600] ; } Sptyp ;
extern Sptyp * sps_list ;
extern int read_next_line (char * ) ;
extern int nod_p2t [MAXNODES] ; 
extern char bltype [50] ; 
extern int timeas ;
extern int cost_ends ;
extern int trans_freq [MAXNODES];
extern double trans_relf [MAXNODES];
extern char treeFilename[300] ;
extern char fintreFilename [300] ; 
extern char prefix [50]; 
char ** branch_labels ;
char ** cats_labels ;
char ** sps_names ;
int sps , wrong = 0 ;
extern int nuspecs ;
extern int do_resample ;
extern int do_deca;
extern double support [MAXNODES]; 
extern int transformations [MAXNODES] ;

int goto_printree_support () ; 

void alloc_sps_names (int nuspecs){
 int i ;     
 sps_names = malloc   (  nuspecs * sizeof(char *) ) ;
 for (i = 0; i < nuspecs ; i ++){
  sps_names[i]  = malloc ( 300 * sizeof(char) ) ; }
}

int goto_read_tree (int pecies)
{

int   * numernod, * treenod, nunod,anod, c, especs ;
char   bufer [5000] ;

numernod = &nunod;
treenod = &anod;
alloc_sps_names (pecies);

    while (1) {
     if (( input_file = fopen (treeFilename,"rb") )== NULL) {
        printf ("\nError. \"%s\" not found in spasos folder",treeFilename);
        return (0); }
     else
      break ;}

 if (!is_format(bufer)){
     printf ("\nError. Tree file with wrong format. The first line should be 'tread' ");
     fclose(input_file);
     return (0); }

nt = * numernod = * treenod = nuspecs;

ances [ *numernod  ] = -1   ;
sps =  0 ;
c= fgetc (input_file) ;
     while ( isspace (c ) )
       c = fgetc (input_file) ;
     if ( c  == EOF )
       return  ( 0 ) ;
 if ( c == '(' ){
   lefpar ++ ;
   if ( ! (especs = read_tree (numernod  ,treenod) )){
    printf ("\nProblems while reading the tree");
     return  ( 0 )   ; }
      }
if (especs !=nuspecs ){
  printf ("\nError. Number of species in dataset (%i) is different from number of species in tree file (%i)",nuspecs,especs);
  return ( 0 ) ;}
    

if ( lefpar != derpar )
  {
    printf ("\nUnbalanced parenthesis");
    return ( 0 ) ;
  }

nnods = ( 2* sps ) - 1 ; 
intnods = nnods - nt ;


generate_sis ( ) ;
make_optlist ( ) ;
return ( 1 ) ;

}

int is_format (char *bufer) {
    char bifer [5000];
    int i ;
    strcpy (bifer,bufer);
    while (1){
         i = read_next_line (  bifer );
         if (!i)
           return ( 0 ) ;
         strlwr (bifer);
         if ( strstr(bifer,"tread" )!= NULL )
            return ( 1 ) ;}
 }


int read_tree (int  * numernod , int *  treenod ) {
int c,i,gsps;


   while (1){

       c= fgetc (input_file) ;

       while ( isspace (c ) )
         c = fgetc (input_file) ;
       if ( c  == EOF || c == ';' ){
        wrong = 1; return ( 0 )  ; }
       if ( ( c !='(' ) && ( c !=')' )  )
        {
         i = 0 ;
         while (  (!(isspace (c))) && (c != ')' ) && ( c != '('  ))
         {
          if (c == -1){
          wrong=1;
          return (0) ;}
           sps_names [sps][i] = c ;
             i++ ;
             c = fgetc (input_file) ;}
           ungetc (c,input_file);
           sps_names [sps][i] = NULL ;
           gsps = match_name (sps);
           if (gsps == -1){
            wrong = 1;
            return (0);
              }
           ances [ gsps ] = *treenod;
           sps ++ ;
           nuters ++ ;

         continue ;
         }
       if (c == ')'){
         derpar ++ ;
         * treenod = ances [ *treenod ]  ;
         if ((*treenod) == 45)
             printf("");
         break ;
         }
       if ( c == '(' ){
           lefpar++;
           (*numernod)++ ;
           ances [ *numernod ] = *treenod  ;
           *treenod = *numernod ;
           if ((*treenod) == 45)
             printf("");
          read_tree ( numernod , treenod ) ;

       }
     }
     if (wrong)
       return (0) ;
     return ( sps ) ;
}


match_name (int sps) {
int a ;
char * namo;
namo =  sps_list[0].sps_name ;
 for (a= 0 ; a < nuspecs ; a ++){
     if (!strcmp(sps_names[sps],sps_list[a].sps_name ))
       return (a);}
 printf("\n Name  %s  in tree file does not match any name in tps file",sps_names[sps]);
 return (-1);
 }


compose_num ( c  ) {
    int d ,i;
   char numero [ 5 ]  ;
   numero [ 0 ] = c ;

      for (i= 1 ; i< 5 ; i ++) {
          d = fgetc (input_file) ;
          if ( d  == EOF )
             return (-1) ;
           if ( isdigit (d) )
             numero [i] = d ;
           else{
            ungetc (d,input_file) ;
            numero[i] ='\0';
             break ; }
      }
      c = atoi (numero) ;
 return (c) ;
 }


generate_sis ( ) {
int i, j , primero, a  ;
for (a = 0 ; a < MAXNODES ; a ++ ){
     sis[a] = -9 ; firs[a] = - 9 ; }
  for (i = nt ;  i < nnods ; i ++) { //lupea los internos
    primero = 0 ;
    for (j = 0 ;  j < nnods ; j ++) { // lupea anc
        if ( ( ances [j] ==  i  ) )
         {
          if  ( primero == 0  )
            {
            firs [ i ] = j ;
            primero ++ ;}
          else
            sis [ firs [ i ] ] = j ;
         }
       }
   }

}

make_optlist ( )
  {
    int incluido [MAXNODES], terminamos =0;  ;
    int a , i, dde = 0, ctos , count  ;
    for (a = 0 ; a < nt ; a ++)
      incluido [ a ]= 1 ;
    for (a = nt ; a < nnods ; a ++)
      incluido [ a ]= 0 ;

 while (1)
 {
    for  (a = nt ; a < nnods  ; a ++)
     {
      ctos = 0 ; count = 0 ;
      if ( incluido [a] == 1) {
         continue ;

         }
      for (i = firs[a] ; i != - 9  ; i = sis [ i  ] )
         {
          ctos ++ ;
          if ( incluido [ i ] )
           count ++ ;
          else
            break;
         }
       if ( ctos == count )
         {
           optlist [dde] = a ;
           dde ++ ;
           incluido [a] = 1;
         }
         if (dde == intnods)
          terminamos = 1 ;
      }
      if (terminamos )
      break;
  }
}

goto_printree (int how)
{

fprintf(output_file,"tread ");
  printree (nt,how) ;
 fprintf(output_file," ; \n");
}

goto_printree_support ()
{

char nombre [300] ;
fprintf(caca_file,"\n tread ");
  printree_support (nt) ;
fprintf(caca_file," ; \n");
fflush(caca_file); 

}


printree ( int nodo, int how )
{
    int a, i  ;
    i = (nt * 2 )- 1 ;
    fprintf (output_file,"(" ) ;
    for ( a = 0 ; a < (i) ; ++ a )
     if ( ances[a] == nodo )
      if ( a < nt ){
        if ( how )
         fprintf(output_file,"%i=%s ",a,branch_labels[a]);
        else
         fprintf(output_file,"%i=_nd ",a);
      }
      else
       printree ( a,how );
   if (nodo == nt)
    if (how)
      fprintf (output_file,")=");
    else
      (output_file,"))");
   else
     if (how)
      fprintf (output_file,")=%s ",branch_labels[nodo]);
     else
      fprintf (output_file,")=%i_nd ",nodo);
}


printree_support ( int nodo )
{
    int a, i  ;
    i = (nt * 2 )- 1 ;
    fprintf (caca_file,"(" ) ;
    for ( a = 0 ; a < (i) ; ++ a )
     if ( ances[a] == nodo )
      if ( a < nt ){
        fprintf(caca_file,"%i=%s",a,branch_labels[a]);
        if (transformations[a] != 0){
         if (do_resample && do_deca)
           fprintf(caca_file,"\\%.0f/%.1f",trans_relf [a],support [a]) ;
         else
          if (do_deca)
           fprintf(caca_file,"\\-/%.1f ",support [a]) ;
          else
           if (do_resample)
             fprintf(caca_file,"\\%.0f/- ",trans_relf [a]) ;}
         fprintf(caca_file," ") ;    
        }  
      else
       printree_support ( a );
   if (nodo == nt)
      fprintf (caca_file,")=");
   else{
    if (transformations[nodo] != 0){ 
       fprintf (caca_file,")=n%i/%s",nod_p2t[nodo],branch_labels[nodo]);
       if (do_resample && do_deca) {
         fprintf (caca_file,"\\%.0f/%.1f",trans_relf[nodo],support[nodo]);}
       else
        if (do_deca)
          fprintf (caca_file,"\\-/%.1f",support[nodo]);
        else
         if (do_resample)
          fprintf (caca_file,"\\%.0f/-",trans_relf[nodo]);
       }
        else
          fprintf (caca_file,")=%i",nod_p2t[nodo]); 
    fprintf(caca_file," ") ;
     }

}

int equal_parentheses (){
int c, numsp= 0, open = 0, close = 0  ;

c= fgetc (input_file) ;
while ( isspace (c ) )
  c = fgetc (input_file) ;
   if (c != '(' )
     return (0);
   else
     open ++ ;
 while (1) {
    c = fgetc (input_file) ;
    if  ( c == EOF)
      break ;
    if ( c== '(' )
      open ++ ;
    if (c == ')')
     close ++ ;
  }
   if (close != open)
     return (1);
return (2);
}


















