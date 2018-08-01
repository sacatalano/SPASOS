#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include "forlan.h"

#include <windows.h>
#include <windowsx.h>
#include <stdlib.h>
//#include "ibm.h"
#include <io.h>
#include "winbase.h"
#include "process.h"
#include <winuser.h>
#include "commdlg.h"
#include "commctrl.h"
#include "wingdi.h"
#include "winsock.h"
#include <tchar.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <ctype.h>
#include <unistd.h>
#include <direct.h>
#include <limits.h>


#define CURSUM  \
     sqrt ( ( ( Izq.x - middle->x ) * ( Izq.x - middle->x ) ) + \
            ( ( Izq.y - middle->y ) * ( Izq.y - middle->y ) ) + \
            ( ( Izq.z - middle->z ) * ( Izq.z - middle->z ) ) ) + \
     sqrt ( ( ( Der.x - middle->x ) * ( Der.x - middle->x ) ) + \
            ( ( Der.y - middle->y ) * ( Der.y - middle->y ) ) + \
            ( ( Der.z - middle->z ) * ( Der.z - middle->z ) ) ) + \
     sqrt ( ( ( Anc.x - middle->x ) * ( Anc.x - middle->x ) ) + \
            ( ( Anc.y - middle->y ) * ( Anc.y - middle->y ) ) + \
            ( ( Anc.z - middle->z ) * ( Anc.z - middle->z ) ) ) ;
#define SLIDE_POINT( which , iz , de , an ) \
    X_Der = which - iz ; \
    if ( X_Der < 0 ) X_Der = -X_Der ; \
    X_Izq = which - iz ; \
    if ( X_Izq < 0 ) X_Izq = -X_Izq ; \
    if ( X_Izq < X_Der ) X_Der = X_Izq ; \
    X_Izq = which - an ; \
    if ( X_Izq < 0 ) X_Izq = -X_Izq ; \
    if ( X_Izq < X_Der ) X_Der = X_Izq ; \
    k = 1 ; \
    while ( 1 ) { \
        X_1 = CURSUM ; \
        which += ( X_Der * k ) ; \
        X_3 = CURSUM ; \
        if ( X_3 >= X_1 ) {  \
            if ( X_3 - X_1 < Cte_prop ) break ; \
            X_Der /= 2 ;   \
            which -= ( X_Der * k ) ; \
            k = -k ; }}

HWND hwnd ;
FILE * input_file ;
FILE * output_file , *tmp_file , *trans_tmp_file, * sank_file, * svg_file , * caca_file  ;
char outputFilename[300]  ;
char inputFilename[300] ;
char treeFilename[300] ;
char finalFilename [300] ;
char fintreFilename[300] ;
char otherFilename[300]  ;
char asisFilename [300] ;
char tntexe[ 2000 ] ;

typedef struct { double x, y, z ; } Punktyp ;
typedef struct  {
     Punktyp *pt   ;
     double age ;
     double std_sp_age ;
     double age_aln ;
     char sps_name [ 300 ] ;
     int sp_number ;
     int confnumber ;
     int ind_number;
     int nulands ;
     int which_class ;
     int which_hyp_class ;
     int which_str_class ;
     int which_aln_class ; } Conftyp ;

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

typedef struct {
     double score_shft [ 1000] ;
     double score_str [ 1000 ] ;
     double score_str_inv [ 1000 ] ;
     double score_asis ;
     double score_sh_str [ 1000 ] ;
     double score_str_sh [ 1000 ] ;
     int best_stri ; 
     int best_shft ; 
     int best_str ;  
     int best_sh_str ;
     int best_str_sh ;
     int what_best ; // 0 = asis, 1= shift, 2 str; 3 stri; 4 double_str ;
     double best_overall  ; } Sank_spcelltyp ;

typedef struct {
     Punktyp * pt ; int numrecs ;
      } Landcelltyp ;

extern int goto_read_tree () ;
extern int goto_printree (int) ;
extern int goto_printree_support () ;
int intnods,  nt ;
extern int nnods ;
extern int firs [ MAXNODES ], sis  [ MAXNODES ],optlist[ MAXNODES ], ances [MAXNODES];

double min_cont [MAXNODES],max_cont [MAXNODES] ;

int WAT_CHG ;
int replications = 100 ;
int nuspecs, nod_t2p [MAXNODES],nod_p2t [MAXNODES], transformations [MAXNODES], transform_rnd [MAXNODES][MAXRANDOM],guich_rnd [MAXNODES][MAXRANDOM],guich_map [MAXNODES]  ; // aca hay que alocar dinamicamente transform
int all_trans [MAXNODES][6],bak_all_trans [MAXNODES][6] ; // last cel= ambig/no ambig
double penalty  ;
int penalize = 1, do_resample, do_deca ;
int traffo [1000], pen_fac =1 ;  
char ** branch_labels, ** cats_labels, ** transf_label ;
int trans_freq [MAXNODES], nuconf_sp_clas [300][50], timeas,doshift, dostre, doinvstre, doshstre, doasis= 1, opt_asis, cost_ends = 0, pen_ext = 0 ;
double trans_relf [MAXNODES];
char altype [50], bltype [50], prefix[50] ;
int desc [ MAXNODES ], dde = 0 ;
double brnch_scor [MAXNODES] ;

int trece= 0 , dos= 0 , OUTGRP ;  
double core,  scor_AS_TNT,scor_H_TNT, scor_H_FS, scor_AS_reco,scor_AS_FS ;

int ** final_states=NULL, ** recons=NULL,  totrecs, ruta,  * ispoli, * opt_recons, numrecos, where [MAXNODES] ;
double mincost(int  , int    ) ;
double land_diff      (Punktyp * , Punktyp * ) ;
double pair_conf_dist (Punktyp * , Punktyp * ) ;
double truncate (double ) ;
double maxdists [ 500 ];
void generate_output_file (int,char*) ;
int borrar_espacios(char *  ) ;
void put_cats_inlabels (int cats) ;
void define_final_states ( int ) ;
int my_spawn_hetero () ;
int my_spawn_asis () ;
void fill_alignment_w_consense_doall(int guichsp,int nucats, int doall)  ;
void alloc_consense_matrix (int,int,int) ;
void alloc_optimus_matrix (int,int,int) ;
void alloc_sank_mtx ( ) ;
void test_sank_mtx();
void generate_sank_mtx(); 
void alloc_downcosts ( ) ;
void alloc_upcosts ( );
void alloc_final_states ()  ;
void alloc_ispoli () ;
void alloc_branch_labels ();
void define_limits ( int , int) ;
void alloc_buff_traj(int) ;
void dealloc_buff_traj (int) ;
void calculate_penalty ( int,int ) ;
void put_best_score (int) ;
double sank_downpass () ;
void  sank_uppass () ;
void check_ambiguity (); 
void make_d_stretchs_recat (  );
void define_limit_stretch (  int , int , int  ) ;
int sorting_confs_in_cats_stretch ( int , int , int, int , int,int  ) ;
int fill_w_consense_stretch (int ,int, int,int,int) ;
void fill_doc1_w_consense_asis ( int, int ) ;
void giveme_help (  ) ;
void round_aln_limits () ;
void generate_aln_file(int ,int  );
int r_stretchs (int); 
void fill_consense_matrix_resample(int,int,int);
int define_d_pairings( int, int, int);
void generate_tps_shift (int) ;
int accept_sh_str(int,int); 
void complete_all_trans ();
void generate_species_classif_recat (int );
void conf_x_categ (int,int); 
void cpy_one (int,int) ;


int fill_reconstructions (int) ;
double fill_reconstructions_new (int) ;
int sorting_confs_in_cats ( int , int , int,int ) ;
void make_d_shifts (int,int,int) ;
void make_stretch (int,int,int,int);
void make_stretch_inv (int,int,int,int);
void map_changes (int, int) ; 
int define_dimensions () ;
void define_relative_ages (int nuspec   ) ;
void minmax_age_sp (int  ) ;
void make_as_is (int, int, int, int ) ;
int read_data();
void generate_alignment_asis (int,int ) ;
int generate_alignment_recat ( int, int ) ;
void dealloc_branch_labels () ;
void dealloc_datamatrix ( int ) ;
void dealloc_consense_matrix ( int, int, int )  ;
void dealloc_sank_mtx () ;
void dealloc_downcosts () ;
void dealloc_final_states () ;
void dealloc_recons () ;
void alloc_recons () ;
void define_limits_alignment_cont (  int ) ;
void alloc_alignment (int , int  );
void generate_alignment_pair (int,int) ;
void showme_apair ( int spa, int spb,int nucas,int reco) ;
void conf_by_categs(int nuspec,int nucateg);
void dofermatpoint_3d ( Punktyp , Punktyp , Punktyp , Punktyp * ) ;
void dofermatpoint_2d ( Punktyp , Punktyp , Punktyp , Punktyp * ) ;
void make_d_shifts_menage_trois (int,int,int,int);
int all_desc(int);
void jusout ();
double define_d_pairings_recat (int qreco,int nucas) ;
int improve_optimization() ;
double make_d_shifts_penalty (int ,int ) ;
double make_d_shifts_tripet (int,int,int,int,int);
double make_d_shifts_tripet_both (int,int,int,int,int);
double make_d_shifts_tripet_int(int,int,int,int,int);
double score_by_branch (int asis) ;
double limits [MAXNODES] [60], limits_str [MAXNODES],limits_aln [MAXNODES] [60],limits_aln_reca [MAXNODES],  **downcosts=NULL, *upcosts=NULL, mincosto  [MAXNODES], refer_score, max_modif ;
double score_asis , score_hetero ;
double  escor_fermat (Punktyp * Left, Punktyp * Right,  Punktyp * Anc,  int, int  );
double Distanciero_3d (double X2, double Y2, double Z2, double X1, double Y1,double Z1);
double Distanciero_2d (double , double , double , double ) ;
void bakap_all_trans () ;
double score_in_docks (int nucats, int quehago ,int  invertido, int chgend) ;
int check_cats(); 

int procargs (int, char**);
int process_datafile ();
void do_output_prefix() ;
void show_indiv_list ();
int alloc_matrices () ;
void generate_dock (int);
void fill_sankoff_costs(int,int) ;
void put_best_score (int) ;
void triangle_ineq ();
void jusout ();
void optimize_tree_asis (int) ;
void do_supports () ;
int my_spawn_tree_svg() ;
int optimize_tree_hetero (int) ;
void dealloc_matrices () ;
int read_sps_data (char * , int , int ) ;
int read_age_data (char * , int , int ) ;
void avg_aln_age (int   );
void do_nd_runtntfile_for_age (int   );
void generate_age_covariates (int  );
void calculate_consensus_recat (int  ,int   );
void calculate_aln_ages (int ) ;
void map_support(int  , double  );
void generate_d_svg (int  ,int  ) ;
void  sort_configs_aln_recat (int  );
int read_tmp_cont(int);
void generate_tmp_file_hetero () ;
int  read_tmp_data_recat(int ) ;
void define_limit_db_stretch(int,int,int,int) ;

int translator_sh [100], translator_str [100],translator_strinv [100], translator_sh_str[2][1000],translator_str_sh[2][1000], jumany_sh, jumany_str, transo ;
int cattotri [3][100] , mask_aln[100][100];
int dde_cns_mtx ,mobes [5] , mejoro [200] ;

void build_extended_states(int nuspecs, int nucateg);
int calculate_nustates(int);
int extended = 0;

void alloc_branch_labels ();
void dealloc_branch_labels () ;
double calculate_max_modif (int,int);

void dealloc_datamatrix (int) ;
void fill_consense_matrix (int, int, int) ;
Conftyp * dock1, * dock2, * buff_dock ;
Conftyp ** buff_traj, * bes_traj ;
double fermat_scale= 0.001, esco , scor_improved;
Conftyp * datamatrix, **align_matrix ;
Sank_spcelltyp ** sank_mtx ;
Conftyp ** consense_matrix, ** optimus_matrix  ;
Sptyp * sps_list ;
Punktyp * pt1, * pt2 ;

int b,skip_optim=0, contlin = 0, dimens = 2, yes [ 100 ][ 100 ] , yes_str [ 100 ], nuconfs,nuland,NUCATEG,nuspecs,dime, inf_limit [MAXNODES], sup_limit [MAXNODES], position [100], stretch_value [ 100 ] ;
int doskfile= 0, doasisfiles= 0, do_classif= 0 , do_covfile=0 ,  maxstages= 0,dosvg= 1, dospeclist= 0, outusrname=0;
int givages = 0, cat_alin;
double inf_limit_cont [MAXNODES], sup_limit_cont [MAXNODES]  ;
int CONFS, DIMS, LANDS, STATES ;
char archivo [ 50 ] ;
double support [MAXNODES];


int main (int argc, char * argv[])
{
 int i= 0 , h ,  a= 0 , b,  tadde, dde,  doall,catal, max ;
 int  yeso;

 for (h = 0 ; h < 200 ; h ++)
   mejoro [h] = 0;
if (!procargs ( argc , argv ) )
 return (0) ;
 penalize = 1 ;
if (process_datafile() == 0)
  return (0);
if (!goto_read_tree (nuspecs)){
    return ( 0 ) ; }

if (timeas)
  doall = 1 ;
 else
  doall = 0;
cost_ends =  0 ;
if (doall){
    doshift = 1 ;
    dostre = 1 ;
    doinvstre = 1 ;
    doshstre = 1 ;}
 else{
      doshift = 1 ;
     dostre = 0 ;
    doinvstre = 0 ;
    doshstre = 0 ;}

 input_file = fopen (inputFilename,"rb") ;
 a = 0 ;
  if (nuspecs != nt )
   printf("\n tps and tree files have different number of species: %i vs. %i respectively ",nuspecs,nt);
 if (extended )
    STATES = calculate_nustates(nuspecs);
 else
    STATES = nuspecs ;

printf("\nPre-processing...");

yeso = 0; max = 0 ;
 if (timeas){
      minmax_age_sp (nuspecs) ;  
     define_relative_ages ( nuspecs ) ;  
     if (NUCATEG > 0 ){
       define_limits ( NUCATEG , nuspecs ) ;  
       yeso= sorting_confs_in_cats ( NUCATEG , nuspecs , CONFS,1 ) ;  
       if (!yeso){
       return (0);}
       }
    else{
      for (i= 4 ; i < 31 ; i++) {
         define_limits ( i , nuspecs ) ;  
         yeso= sorting_confs_in_cats ( i , nuspecs , CONFS,0 ) ;  
         if (yeso)
          max = i ; }
         if ( max < 3){
           printf("\n The file has less than three stages for some species. The analysis cannot be performed");
           return(0);}
          else{
           NUCATEG = max;
           define_limits ( max, nuspecs ) ;
           yeso= sorting_confs_in_cats ( max , nuspecs , CONFS,1 ) ;}
         }
       }
  else
    yeso= sorting_confs_in_cats ( NUCATEG , nuspecs , CONFS,1 )  ;




do_output_prefix() ;

 printf("\r                                  ");
 printf("\nSettings:");
 printf("\n---------");
 if (timeas)
   printf("\nAge given in continuos scale") ;
 else
   printf("\nAge given as a priori defined stages") ;
 printf("\nNumber of Specimens: %i",nuconfs ) ;
 printf("\nNumber of landmarks: %i in %iD",LANDS, DIMS) ;
 printf("\nNumber of Species: %i", nuspecs ) ;
 printf("\nNumber of Stages: %i", NUCATEG ) ;
 printf("\nPenality factor= %i",pen_fac);

if (dospeclist)
   show_indiv_list ();


alloc_matrices ();

tadde = NUCATEG   ;
generate_dock (NUCATEG);

dde = 0 ;



fill_consense_matrix ( nuspecs, NUCATEG, LANDS) ;
dde_cns_mtx =nuspecs ;
if (extended)
  build_extended_states(nuspecs, NUCATEG) ;

max_modif = calculate_max_modif (NUCATEG,nuspecs) ;
alloc_buff_traj(NUCATEG) ;



transo = 0 ;
for( a = 0 ; a < STATES  ;a ++ )
   for ( b = 0 ; b < STATES  ;b ++ ){
      if (a == b ) continue ;
         make_as_is (a,b,NUCATEG,STATES) ;}

 if (penalize)
  calculate_penalty (nuspecs,NUCATEG ) ;
 else
  { penalty = 0 ;  pen_fac= 0 ;}

printf("\nRunning the analysis...");

fill_sankoff_costs(nuspecs,NUCATEG) ;
put_best_score (NUCATEG) ;


triangle_ineq ();

if (doskfile){
    test_sank_mtx(); 
 generate_sank_mtx();  }
    

jusout ();

if (doasisfiles)
  optimize_tree_asis (doall) ;
else
 catal  = optimize_tree_hetero (doall) ;
bakap_all_trans () ;
check_ambiguity() ;

do_supports () ;

my_spawn_tree_svg() ;



fflush(stdout);
dealloc_matrices () ;
free (align_matrix) ;  
free ( sps_list ) ;
free ( dock1 ) ;
free ( dock2 ) ;
free ( buff_dock ) ;
free (upcosts) ;

fflush(stdout) ;
printf("\r                                    ");
printf("\nDONE!!!");

return(0) ;
} //main



void bakap_all_trans (){
int i, n ;

for (n= 0 ; n < nnods ; n++)
 for (i=0; i < 6 ; i++)
  bak_all_trans [n][i] = all_trans [n][i] ;
  
}



int read_next_line (  char * bafer )
{
    int cter ;
    cter = fgetc (input_file)  ;
    while ( isspace (cter) )
        cter = fgetc (input_file) ;
     if ( cter == EOF ){
      return (0) ;  }
     ungetc (cter,input_file) ;
     fgets (bafer,10000,input_file) ;
     contlin ++ ;
     return (1) ;
}// read_next_line

int save_configuration ( int guichconf, int dimes, int nland, char * bafer)
{
 int l = 0,  ctos, rsd = 0 ,baflen , j ;
 double uno , dos, * pt_edad, tres ;
 char  * pt_spname,  * pt_char ;
 Punktyp * pt = datamatrix[guichconf].pt ;
 pt_spname = datamatrix[guichconf].sps_name  ;
 pt_edad=& datamatrix[guichconf].age ;

 datamatrix[guichconf].confnumber = guichconf ;
 datamatrix[guichconf].nulands = nland ;
    for (l = 0 ; l < nland ; l++){
      if (!read_next_line ( bafer) )
         return (0)  ;
      else {

         pt_char = bafer  ;
         ctos = borrar_espacios(pt_char) ;
         pt_char += ctos ;
         if (!isdigit (* pt_char) && ( * pt_char != '-')  ){
           printf ("\nError! Specimen %i has less than %i lands (line %i)",guichconf,nland,contlin);
           return (0); }
         else{
             if (dimes == 2){
              j= sscanf ( bafer,"%lG%lG",&uno,&dos);
              if ( j < 2 ){
                 printf ("\nError! Specimen %i less than two coordinates for landmark %i (line %i)",guichconf,l,contlin);
                 return (0); }
               ;
              pt->x= uno ; pt->y = dos;
             }
             else{
               j= sscanf ( bafer,"%lG%lG%lG",&uno,&dos,&tres) ;
               if( j != 3 ) {
                 printf ("\nError! Specimen %i has less than three coordinates for landmark %i (line %i)",guichconf,l,contlin);
                 return (0); }
              pt->x= uno ; pt->y = dos;pt->z = tres;}
       
           pt ++ ;
           }
          }
         }

          rsd = 0 ;
          while (read_next_line ( bafer)){
              pt_char = bafer  ;
              baflen = strlen (pt_char);
             rsd = read_sps_data(pt_char,guichconf,baflen) ;
             if ( rsd == -1)
                 return(0);
             else
               if (rsd == 0 )
                 continue ;
               else
                 break ;}
           rsd = 0 ;
          while (read_next_line ( bafer)){
             pt_char = bafer  ;
             baflen = strlen (pt_char);
             rsd = read_age_data(pt_char,guichconf,baflen) ;
             if ( rsd == -1)
                 return(0);
             else
               if (rsd == 0 )
                 continue ;
               else
                 break ;}


   return (1) ;
}// save_configuration      


int read_sps_data(char * pt_chr, int guichconf, int largo){
int ctos, u,a,  i, ind,  j ;
char * pt_orig, * pt_l,stri[100] ;
   pt_orig = pt_chr ;
  if (isdigit (* pt_chr)  ){
       printf ("\nError! Specimen %i has more than %i lands (line %i)",guichconf,LANDS,contlin);
   return (-1); }
   for(i = 0; i<100; i++)
     stri[i] = tolower(pt_chr[i]);
  //if  ( ( strstr ( pt_chr,"LM=") != NULL ) || ( strstr ( pt_chr,"AGE=")   != NULL  ) || ( strstr ( pt_chr,"LM3=") != NULL ) )  {
  if  ( ( strstr ( stri,"lm=") != NULL ) || ( strstr ( stri,"age=")   != NULL  ) || ( strstr ( stri,"lm3=") != NULL ) )  {
        printf ("\nError! Specimen %i lacks species information(line %i)",guichconf,contlin);
        return (-1); }
  else
   if (  strstr ( stri,"id") != NULL )
     if ( (pt_chr= strstr ( pt_chr,"=")) != NULL )
      {
        pt_chr++ ;
        ctos = borrar_espacios(pt_chr) ;
        pt_chr += ctos ;
        u=0 ;
        ind = 1  ;
        if ((pt_chr - pt_orig  ) == largo) {
          printf("\nError! No species name at line %i specimen %i ",contlin,guichconf);
            return (-1);}
        if ( strchr ( pt_chr, '/')  == NULL) {
           strcpy(datamatrix[guichconf].sps_name,pt_chr)  ;
           pt_l = datamatrix[guichconf].sps_name ;
           for (a = 0 ; a < 300 ; a ++ ) {
              if ((* pt_l) < 33 ){
                 datamatrix[guichconf].sps_name[a] = '\0' ;
                 return (1) ; }
               pt_l ++ ;   }
              }
        else {
          for ( j = (pt_chr - pt_orig) ; j < largo ; j++){
           if (* pt_chr == '/')
             break ;
              datamatrix[guichconf].sps_name[u] =* pt_chr ;
               u ++ ;
               pt_chr++;
            }
          datamatrix[guichconf].sps_name[u] ='\0' ;
          if (j != u){
             pt_chr ++ ;
           datamatrix[guichconf].ind_number = atoi (pt_chr) ;}
       return ( 1 ); }}
    else
      return ( -1 );
      return(1) ;
 }

int read_age_data(char * pt_chr, int guichconf,int largo){
int ctos ,i ;
char * pt_orig, stri[100] ;
   pt_orig = pt_chr ;
   for(i = 0; i<100; i++)
     stri[i] = tolower(pt_chr[i]); 
 //if (  (strstr ( pt_chr,"LM=") != NULL) || (strstr ( pt_chr,"LM3=") != NULL)  )  {  //FLAG        
   if (  (strstr ( stri,"lm=") != NULL) || (strstr ( stri,"lm3=") != NULL)  )  {  //FLAG
        printf ("\nError! Specimen %i lacks age information(line %i)",guichconf,contlin);
        return (-1); }
   else
    if ( (strstr ( stri,"age=") )  != NULL ){
         pt_chr+= 4 ;
         ctos = borrar_espacios(pt_chr) ;
         pt_chr += ctos ;
         if ((pt_chr - pt_orig  ) == largo) {
          printf("\nError! No age for specimen %i at line %i  ",guichconf,contlin);
            return (-1);}
         if (!isdigit(pt_chr[0])){
           printf ("\nError while reading the Age of specimen %i. Char. \"%c\"  found (line %i)",guichconf,pt_chr[0], contlin);
           return (-1); }
         datamatrix[guichconf].age = atof (pt_chr) ;
         return ( 1 ) ; }
    else
      return (0);
}

int borrar_espacios (char * ptchar){
 int ctos=0 ;
 while (isspace (* ptchar)  ){
    ctos ++ ;
    ptchar ++ ;  }
  return (ctos)   ;
}

int count_species (int confs) {
 int i, j,  espec, dde, guere= 0 , diff;
 espec = 1 ;

sps_list= (Sptyp * ) malloc (confs * (sizeof (Sptyp))) ; 
for (i= 0; i< confs; i ++)
   sps_list[i].sps_name  = (char*) malloc ( 300 * sizeof(char) ) ;  

sps_list[0].sps_name = datamatrix[0].sps_name ;
sps_list[0].sp_number = 0 ;
sps_list [0].conflist[0] = 0 ;
dde = 1 ;
guere = 1 ;

espec =  1 ;
for (i = 1 ; i < confs; i ++)
    {
    diff = 0 ;
    for (j = 0 ; j < espec; j ++)
      if ( (strcmp (datamatrix[i].sps_name,sps_list[j].sps_name) !=0))
         diff++ ;
      if ( diff == espec){
        sps_list[ espec ].sps_name = datamatrix[i].sps_name ;
        espec ++ ; }
    }


 for (j = 0 ; j < espec; j ++){
   guere = 0   ;
   for (i = 0 ; i < confs; i ++){
     if ( (strcmp (datamatrix[i].sps_name,sps_list[j].sps_name) ==0)){
           sps_list [j].conflist[guere] = i ;
           datamatrix[i].sp_number = j ;
           sps_list [j].sp_number = j ;
           guere ++ ;
          }
     sps_list [j].num_confs = guere ;}
   }

return (espec ) ;
}



void minmax_age_sp (int nuspecs )
 {
   int i, cual=0,j ;
   Sptyp * pt_sp ;
   Conftyp * pt_conf ;
   pt_sp = sps_list ;
   pt_conf = datamatrix ;

   for (  i = 0 ;   i < nuspecs ; i ++ ) {
      pt_sp[i].min_age = 10000000000 ;
      pt_sp[i].max_age = -1000000000 ;
      for (j = 0 ;  j < pt_sp[i].num_confs  ; j ++) {
        pt_conf[cual].sp_number = pt_sp[i].sp_number ;
        if (pt_conf[cual].age < pt_sp[i].min_age )
             pt_sp[i].min_age = pt_conf[cual].age ;
        if (pt_conf[cual].age > pt_sp[i].max_age )
             pt_sp[i].max_age = pt_conf[cual].age ;
             cual ++ ;  }}


 }


void define_relative_ages (int nuspec   ) {
int i , j , cual = 0 ;
Conftyp * pt_conf ;
Sptyp * pt_sp ;

pt_conf= datamatrix ;
pt_sp = sps_list ;

for (  i = 0 ;   i < nuspec ; i ++ ) {
   for (j = 0 ;  j < pt_sp[i].num_confs  ; j ++) {
         pt_conf[cual].std_sp_age =  (pt_conf[cual].age - pt_sp[i].min_age)  / (pt_sp[i].max_age - pt_sp[i].min_age)  ;
         cual ++ ; } }
}


double pair_conf_dist (Punktyp *  pt1, Punktyp * pt2)
{
  double score = 0  ;
  int i , nlan ;
  if (trece && dos)
    printf("\n---------------");
  nlan = datamatrix [0].nulands ;
  for (  i = 0 ;   i < LANDS ; i ++ ) {
      score += land_diff (pt1, pt2);
      pt1 ++ ; pt2++; }
return (score);
}

double land_diff ( Punktyp *  pnt1, Punktyp * pnt2 ){
 double un, dos, tres, cuatro ;
 un  = ( pnt2->x - pnt1->x )  ;
 dos  = ( pnt2->y - pnt1->y ) ;
 if ( DIMS == 3 ) {
  tres =  ( pnt2->z - pnt1->z ) ;
  cuatro = un * un + dos * dos + tres * tres  ;
  cuatro = sqrt (cuatro) ;
  }
 else{
  tres  = un * un + dos * dos   ;
  cuatro = sqrt ( tres) ; }
return (cuatro) ;
}

void define_limits (int nucateg, int nuspec){ // define los limites de las categorias por especie
int lims, i, j   ;
double span ;
lims = nucateg + 1   ;
for (i = 0 ; i < nuspec ; i ++ )  {
     span = ( sps_list[i].max_age - sps_list[i].min_age )  / ( lims - 1 );
       for (j = 0 ; j < lims    ; j ++ ){
          limits [i][j] = sps_list[i].min_age    + (  span * j )  ;
          }}
 }




int sorting_confs_in_cats (int nucats, int nusp, int nuconf, int unique ){
int i, j , cual=0, k,edad;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_conf = datamatrix ;
pt_sp = sps_list ;
for (  i = 0 ;   i < nusp ; i ++ )
 for (j = 0 ;  j < nucats  ; j ++)
  yes [i][j] = 0 ;
for (j = 0 ;  j <  nuconf     ; j ++)
  pt_conf [j].which_class = -1 ;


for (  i = 0 ;   i < nusp ; i ++ )
   {
     for (j = 0 ;  j < pt_sp[i].num_confs  ; j ++)
        {
          cual = pt_sp[ i ].conflist [ j ] ;
          for (k = 0 ;  k < nucats  ; k ++)
          {
           if (timeas)
            {
             if ( k == 0) {  
                if ( ( pt_conf[cual].age >= limits[i][k] ) && (pt_conf[cual].age <= limits[i][k+1] ) )
                 {
                  yes[i][k] = 1 ;
                  pt_conf[cual].which_class = k ;
                  }
             }else
             if ( ( pt_conf[cual].age > limits[i][k] ) && (pt_conf[cual].age <= limits[i][k+1] ) )
              {
               yes[i][k] = 1 ;
               pt_conf[cual].which_class = k ;
              }
            }
           else
            {
             edad = pt_conf[cual].age ;
             if (  edad  ==  k )
             {
              yes[i][k] = 1 ;
              pt_conf[cual].which_class = k ;}
             }
          }
        }
   }

 for (  i = 0 ;   i < nusp ; i ++ )
   for (j = 0 ;  j < nucats  ; j ++)
     if (yes [i][j] == 0 ){
      if ( unique ) {
        if (timeas){
         printf("\n The analysis cannot be performed with the number of stages defined");
          printf("\nNo obs for stage %i (%f-%f) species %i= %s",j,limits[i][j],limits[i][j+1],i,sps_list[i].sps_name);
          printf("\n");
           }
        else{
          printf("\nThe analysis cannot be performed");
          printf("\nNo obs for stage %i species %i",j,i);}}
        return (0) ; }


  return (1) ;
} // isthere_data_for_all_cats


void make_d_shifts (sp1,sp2,nucateg) {
int  i,   j,  l, dde = 0  , categ,w_besco, cat,move  ,guich,stg_star_m,stg_fin_m ;
Punktyp * pts_sp1, * pts_sp2, * ptf_sp1, * ptf_sp2, *pts_sp3 ;
double besco,dist_start,dist_end, score=0,core=0  ;

             for (i = - ( nucateg - 2 ) ; i < ( nucateg - 1)  ; i ++ ){
                 if ( i == 0 ) continue ;
                 translator_sh [dde] = i ;
                 score = 0 ; guich=0;
                 if (cost_ends){
                  if (i < 0 )
                    {
                     categ = 0 ;
                     pts_sp1 = consense_matrix [sp1][categ].pt ; 
                     categ =   ( - i )  ;
                     pts_sp2 = consense_matrix [sp2][categ].pt ; 
                     } else {
                      categ =   i ;
                      pts_sp1 = consense_matrix [sp1][categ].pt ; 
                      categ =  0 ;
                      pts_sp2 = consense_matrix [sp2][categ].pt ; 
                     }
                    if (i < 0 )
                    {
                     categ = cat =   ( nucateg-1) + i ;
                     ptf_sp1 = consense_matrix [sp1][categ].pt ; 
                     categ =    ( nucateg- 1 ) ;
                     ptf_sp2 = consense_matrix [sp2][categ].pt ; 
                     } else {
                      categ = cat= ( nucateg - 1 ) ;
                      ptf_sp1 = consense_matrix [ sp1 ][ categ ].pt ; 
                      categ =  ( nucateg - 1 - i );
                      ptf_sp2 = consense_matrix [ sp2 ][ categ ].pt ; 
                    }

                      dist_start = pair_conf_dist ( pts_sp1 , pts_sp2 ) ;
                      dist_end   = pair_conf_dist ( ptf_sp1 , ptf_sp2 ) ;
                      if ( i < 0 )
                        move = -i ;
                      else
                       move = i ;
                     score = (dist_start + dist_end) / 2  +  penalty  ;
                     if ( i != 0 ) {
                        sank_mtx[sp1][sp2].score_shft[ dde ] = score ;
                        dde ++ ;}
                    }
                    else //if (!cost_ends)
                    {
                      if ( i < 0 )
                       {
                       stg_star_m = -i ;stg_fin_m = nucateg + i  ;
                       for (j = 0 ; j <  nucateg; j++)
                        {
                        if (j < stg_fin_m)
                         {
                         guich = stg_star_m + j ;
                         pts_sp1 = consense_matrix [sp1][j].pt ;
                         pts_sp3 = consense_matrix [sp2][guich].pt ;
                         core = pair_conf_dist (pts_sp1,pts_sp3);
                         score += core ;
                        }
                       }
                      }
                     else
                     {
                      stg_star_m = i ;  guich= 0 ; score=0;
                      for (j = 0 ; j <  nucateg; j++)
                       {
                       if (j >= stg_star_m)
                        {
                        pts_sp1 = consense_matrix [sp1][j].pt ;
                        pts_sp3 = consense_matrix [sp2][guich].pt ;
                        guich++ ;
                        core = pair_conf_dist (pts_sp1,pts_sp3);
                        score+= core;
                       }
                      }
                    }

                   if ( i != 0 ) {
                      if (i<0 )
                        l = -i;
                      else
                         l = i ;
                     score = score / (nucateg-l) ;
                     score = score +  penalty  + ( penalty * ( l - 1) * pen_ext) ;
                     sank_mtx[sp1][sp2].score_shft[ dde ] = score ;
                     dde ++ ;}
                    }
                   }

jumany_sh = dde  ;
besco = 10000000 ;
       for (i = 0 ; i <  dde   ; i ++ ){
           if ( (sank_mtx[sp1][sp2].score_shft[ i ]  < besco)  && (sank_mtx[sp1][sp2].score_shft[ i ]  != -99999 ))
            {
              besco = sank_mtx[sp1][sp2].score_shft[ i ] ;
              w_besco = i ;}
           }
           sank_mtx[sp1][sp2].best_shft = w_besco ;
    
}//make_d_shifts

double make_d_shifts_penalty (int sp1,int nucateg) {
int  i,   j,   categ, cat,guich,stg_star_m;
Punktyp * pts_sp1, * pts_sp2, * ptf_sp1, * ptf_sp2, *pts_sp3 ;
double dist_start,dist_end, score=0,core=0  ;
                 i=1 ; // i =  nucateg - 2 ; //i = 1 ;
                 score = 0 ; guich=0;
                 if (cost_ends){
                     categ= i ;
                      pts_sp1 = consense_matrix [sp1][categ].pt ; //define q celda de la sp 1 en comiezo cdo corro sp2 a la der
                      categ =  0 ;
                      pts_sp2 = consense_matrix [sp1][categ].pt ; //define q celda de la sp 2 en comiezo cdo corro sp2 a la der
                      categ = cat= ( nucateg - 1 ) ;
                      ptf_sp1 = consense_matrix [ sp1 ][ categ ].pt ; //define q celda de la sp 1 en final cdo corro sp2 a la der
                      categ =  ( nucateg - 1 - i );
                      ptf_sp2 = consense_matrix [ sp1 ][ categ ].pt ; //define q celda de la sp 2 en final cdo corro sp2 a la der
                      dist_start = pair_conf_dist ( pts_sp1 , pts_sp2 ) ;
                      dist_end   = pair_conf_dist ( ptf_sp1 , ptf_sp2 ) ;
                      score = (dist_start + dist_end) / 2;
                    }
                    else //if (!cost_ends)
                    {
                      stg_star_m = i ;  guich= 0 ; score=0;
                      for (j = 0 ; j <  nucateg; j++)
                       {
                       if (j >= stg_star_m)
                        {
                        pts_sp1 = consense_matrix [sp1][j].pt ;
                        pts_sp3 = consense_matrix [sp1][guich].pt ;
                        guich++ ;
                        core = pair_conf_dist (pts_sp1,pts_sp3);
                        score+= core;
                       }
                      }
                      score = score / (nucateg - i) ;
                     }

return ( score);
}//make_d_shifts_penalty

void make_stretch (sp1,sp2,nucateg,especies) { //cuando el stretch es negativo se acorta  para la izquierda el desce (queda igual el anc)
int  i,   dde = 0  , categ,w_besco, cat, move ;
Punktyp * pt_sp1, * pt_sp2 ;
double besco,dist_start,dist_end, score   ;
              for (i = - ( nucateg - 2 ) ; i < ( nucateg - 1)  ; i ++ ){
                  if ( i == 0 ) continue ;
                  translator_str [dde] = i ;
                     categ = 0 ;
                     pt_sp1 = consense_matrix [sp1][categ].pt ; //define q celda de la sp 1 en comiezo cdo corro sp2 a la izq
                     pt_sp2 = consense_matrix [sp2][categ].pt ; //define q celda de la sp 2 en comiezo cdo corro sp2 a la izq
                     dist_start= pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                   if (i < 0 )
                    {
                     categ = cat =   ( nucateg- 1 ) + i ;  ;
                     pt_sp1 = consense_matrix [sp1][categ].pt ; //define q celda de la sp 1 en final cdo corro sp2 a la izq
                     categ =    ( nucateg- 1 ) ;
                     pt_sp2 = consense_matrix [sp2][categ].pt ; //define q celda de la sp 2 en final cdo corro sp2 a la izq
                     } else {
                      categ = cat= ( nucateg - 1 ) ;
                      pt_sp1 = consense_matrix [ sp1 ][categ].pt ; //define q celda de la sp 1 en final cdo corro sp2 a la der
                      categ =   ( nucateg - 1 ) - i;
                      pt_sp2 = consense_matrix [ sp2][categ ].pt ; //define q celda de la sp 2 en final cdo corro sp2 a la der
                      }
                   if (i <  0 )
                    move = -i ;
                   else
                    move =  i;
                   dist_end = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                   score = (dist_start + dist_end) / 2 ;
                   score = score +  penalty +  (penalty * ( move - 1) * pen_ext) ;
                   sank_mtx[sp1][sp2].score_str[ dde ] = score ;
                   dde ++;
                   }


jumany_str = dde ; 
besco = 10000000 ;
       for (i = 0 ; i <  dde   ; i ++ ){
           if ( (sank_mtx[sp1][sp2].score_str[ i ]  < besco)  && (sank_mtx[sp1][sp2].score_str[ i ]  != -99999 ))
            {
              besco = sank_mtx[sp1][sp2].score_str[ i ] ;
              w_besco = i ;}
           }
           sank_mtx[sp1][sp2].best_str = w_besco ;
}//make_stretch
void make_d_stretchs_recat (  ) {
 int a , b , c=0 , i , invertido = 0 ,d,adde, sp1 , sp2,dde,  w_besco, j, total,move ;
 double besco= 9999999999, scor,score   ;
 Sank_spcelltyp ** sank_pt ;
 sank_pt = sank_mtx ;


 total = (NUCATEG - 3) * 2   ;

    for (a = 0; a < nuspecs; a++)
     {
        sp1 = a  ;
        dde = 0 ;

       for (i = ( - NUCATEG + 2 ) ; i <  NUCATEG -1  ; i ++ ) 
        {
          if (i == 0 ) continue ;
          translator_str [dde] = i ;
          if (( NUCATEG + i ) <  MINCATS){
             for (c=  0; c < nuspecs ; c ++ )
               sank_pt [c][sp1].score_str[dde] = -99999 ;
               dde ++ ;
             continue;}
          define_limit_stretch (  i , NUCATEG , sp1  ) ;
          if (sorting_confs_in_cats_stretch ( NUCATEG , nuspecs , nuconfs, sp1 , i,0  )) 
           {

            fill_w_consense_stretch (i ,NUCATEG, sp1,invertido,0) ;
            for (b = 0; b < nuspecs; b++)
              {
               sp2 = b ;
               if ( sp1 == sp2 ) continue;
               fill_doc1_w_consense_asis ( sp2, NUCATEG  ) ;
               scor  =  score_in_docks ( NUCATEG , i, invertido,0 ) ;
               if (i < 0 ) move=-i ; else move =  i ;
               scor = scor + penalty + ( penalty *( move - 1) * pen_ext) ;
               sank_pt [sp2][sp1].score_str[ dde ] = scor ;
              } // lup sp b
            }
            else
            {
             for (c=  0; c < nuspecs ; c ++ )
               sank_pt [c][sp1].score_str[dde] = -99999 ;
            }
        dde ++ ;
       } // todas las categs
    } // lup sp a



 /* ACA CALCULO EL PROMEDIO ENTRE LAS DOS TRANSFORMACIONES ASI LOS COSTOS SON SIMETRICOS*/
for (a = 0 ; a < nuspecs ; a ++)
 for (b = a ; b < nuspecs ; b ++)
   {
   if (a == b) continue ;
   for (d = 0 ; d < dde  ; d ++){
      adde = dde - d -  1  ;
     if (sank_mtx[a][b].score_str [d] ==  -99999)
      {
       if (sank_mtx[b][a].score_str [ adde ] !=  -99999)
           sank_mtx[a][b].score_str [d] = sank_mtx[b][a].score_str [ adde] ;
      }
     else
       {
       if (sank_mtx[b][a].score_str [adde ] ==  -99999)
           sank_mtx[b][a].score_str [adde] = sank_mtx[a][b].score_str [d] ;
       else{
          score  = sank_mtx[b][a].score_str [adde] ;
          besco  = sank_mtx[a][b].score_str [ d ] ;
           scor =  (score + besco) / 2 ;
           sank_mtx[b][a].score_str [ adde] = scor ;
           sank_mtx[a][b].score_str [ d    ] = scor ;}
          
       }

 }}

for ( a = 0; a < nuspecs ; a++)
  {
  for ( b = 0; b < nuspecs ; b++)
     {

       if ( a == b ){
        // printf ("   -     " ) ;
            continue ;}
       besco = 99999999;

       for (i = 0 ; i <  dde   ; i ++ )  // no deberia ir total mas 1 ?
          {
           if ( (sank_mtx[a][b].score_str[ i ]  < besco) && (sank_mtx[a][b].score_str[ i ] != -99999) )
            {
             besco = sank_mtx[a][b].score_str[ i ] ;
             w_besco = i ;
            }
           }
       sank_mtx[a][b].best_str = w_besco ;
        j   =  stretch_value [w_besco] ;
     }
  }

}//make_d_stretchs_recat


make_inv_stretchs_recat (  ) {
 int a , b , c=0 , i ,d, sp1 , sp2,dde, invertido=1,  w_besco, j, move, adde  ;
 double besco= 9999999999, scor,score  ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
 Sank_spcelltyp ** sank_pt ;
 sank_pt = sank_mtx ;

pt_conf = datamatrix ;
pt_sp = sps_list ;
    for (a = 0; a < nuspecs; a++){
        sp1 = a  ;  dde = 0 ;
        for (i = ( - NUCATEG + 2  ) ; i <  NUCATEG -1  ; i ++ ){// for (i = (-nucateg + 3 ) ; i <  0  ; i ++ )
          if (i == 0) continue ;
          translator_strinv [ dde ] = i ;
          if (( NUCATEG + i ) <  MINCATS) {
             for (c=  0; c < nuspecs ; c ++ )
               sank_pt [c][sp1].score_str_inv[dde] = -99999 ;
               dde ++ ;
               continue ; }
          define_limit_stretch (  i , NUCATEG , sp1  ) ;
           if (sorting_confs_in_cats_stretch ( NUCATEG , nuspecs , nuconfs, sp1 , i ,1 ))  // las pone en las categs de stret de 0 a x . voy a considerar q
           {                                                                            //se cuentan desde el final de la traject en o de las fciones
            fill_w_consense_stretch (i ,NUCATEG, sp1, invertido,0) ;
            for (b = 0; b < nuspecs; b++)
              {
               sp2 = b ;
               if ( sp1 == sp2 ) continue;
               fill_doc1_w_consense_asis ( sp2, NUCATEG  ) ;
               scor  =  score_in_docks ( NUCATEG , i , invertido,0) ;
               if (i < 0 ) move=-i ; else move = i ;
               scor = scor + penalty + ( penalty *( move - 1) * pen_ext) ;
               sank_pt [sp2][sp1].score_str_inv[ dde ] = scor ;
              } // lup sp b
            }
            else
            {
             for (c=  0; c < nuspecs ; c ++ )
              sank_pt [c][sp1].score_str_inv[dde] = -99999 ; }
        dde ++ ;
       } // todas las categs
    } // lup sp a


 /* ACA CALCULO EL PROMEDIO ENTRE LAS DOS TRANSFORMACIONES ASI LOS COSTOS SON SIMETRICOS*/
for (a = 0 ; a < nuspecs ; a ++)
 for (b = a ; b < nuspecs ; b ++)
   {
   if (a == b) continue ;
   for (d = 0 ; d < dde  ; d ++){
       adde = dde - d -  1  ;
     if (sank_mtx[a][b].score_str_inv [d] ==  -99999)
      {
       if (sank_mtx[b][a].score_str_inv [adde] !=  -99999)
           sank_mtx[a][b].score_str_inv [d] = sank_mtx[b][a].score_str_inv [ adde ] ;
      }
     else
       {
       if (sank_mtx[b][a].score_str_inv [ adde ] ==  -99999)
           sank_mtx[b][a].score_str_inv [ adde ] = sank_mtx[a][b].score_str_inv [d] ;
       else{
          score  = sank_mtx[b][a].score_str_inv [ adde ] ;
          besco  = sank_mtx[a][b].score_str_inv [ d ] ;
           scor =  (score + besco) / 2 ;
           sank_mtx[b][a].score_str_inv [ adde ] = scor ;
           sank_mtx[a][b].score_str_inv [ d    ] = scor ;}
       }

 }}



for ( a = 0; a < nuspecs ; a++)
  {
  for ( b = 0; b < nuspecs ; b++)
     {

       if ( a == b ){
      //   printf ("   -     " ) ;
            continue ;}
       besco = 99999999;

       for (i = 0 ; i <  dde   ; i ++ )// no deberia ser total mas 1 ??
          {
           if ( (sank_mtx[a][b].score_str_inv[ i ]  < besco) && (sank_mtx[a][b].score_str_inv[ i ] != -99999) )
            {
             besco = sank_mtx[a][b].score_str_inv[ i ] ;
             w_besco = i ;
            }
           }
       sank_mtx[a][b].best_stri = w_besco ;
        j   =  translator_strinv [w_besco] ;
     }
  }

 for ( a = 0; a < nuspecs ; a++){
   for ( b = 0; b < nuspecs ; b++){
     if ( a == b ){
    // printf ("  -   " ) ;
     continue ;}
       j = sank_mtx[a][b].best_stri ;
       }}
  for (a= 0 ; a < dde ; a ++)   
    translator_strinv [a] = - translator_strinv [a ] ;   
}//make_inv_stretchs_recat

make_shift_stretchs_recat (  ) {
int a, i , j , c ,d ,k,l, sp2, sp1,    mvs,mvf;
int cto,  invertido = 2 , dde=0 ,w_besco, w ;
double score, scor, besco ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
Sank_spcelltyp ** sank_pt ;
sank_pt = sank_mtx ;
pt_conf = datamatrix ;
pt_sp = sps_list ;


 for (i = - ( NUCATEG - 2 ) ; i < ( NUCATEG - 1)  ; i ++ ){ // categoria de inicio aca sp1 es la que modifico.
   for (j =   - ( NUCATEG - 2 )   ; j < ( NUCATEG - 1)   ; j ++ ){ // categoria de final.
         translator_sh_str [0] [dde] = i ;
         translator_sh_str [1] [dde] = j ;
       dde ++ ;}}

       for (sp1 = 0; sp1 < nuspecs; sp1++){ // lup de la especie a modificar
          for (d = 0 ; d < dde ; d++){
              i = translator_sh_str [0][ d ] ;
              j = translator_sh_str [1][ d ] ;

              if ( ( NUCATEG -i + j ) < MINCATS ){  // que no dividamos en menos de 4 toda la categoria
                for (c=  0; c < nuspecs ; c ++ )
                 sank_pt [c][sp1].score_sh_str[d] = -99999 ;
                continue ; }
              if (!accept_sh_str(i,j) ){
                for (c=  0; c < nuspecs ; c ++ )
                 sank_pt [c][sp1].score_sh_str[d] = -99999 ;
                continue ; }
              define_limit_db_stretch(i,NUCATEG,sp1,j) ;
           cto = -i + j ;
           if (sorting_confs_in_cats_stretch ( NUCATEG , nuspecs , nuconfs, sp1 , cto,invertido  ))  // las pone en las categs de stret de 0 a x . voy a considerar q
           {                                                                            //se cuentan desde el final de la traject en el resto de las fciones
            fill_w_consense_stretch (i ,NUCATEG, sp1, invertido,j) ;
            for (sp2 = 0; sp2 < nuspecs; sp2++)
              {
               if ( sp1 == sp2 ) continue;
               fill_doc1_w_consense_asis ( sp2, NUCATEG  ) ;
               scor  =  score_in_docks ( NUCATEG , i , invertido,j) ;
               mvs = i ; mvf = j ;
               if (( mvs > 0 && mvf > 0 ) || ( mvs > 0 && mvf > 0 )) {
                 if (mvs < 1) mvs = - mvs ;
                 if (mvf < 1) mvf = - mvf ;
                 if (mvf >= mvs ){k = mvf  ;  l = k + (mvf-mvs); }
                 if (mvs > mvf ) { k = mvs ;  l = k + (mvs-mvf);}
                 scor = scor + penalty + ( penalty * ( l - 1) * pen_ext) ;
                 sank_pt [sp2][sp1].score_sh_str[ d ] = scor ;
               }
                else
                  {
                  if (mvs < 1) mvs = - mvs ;
                  if (mvf < 1) mvf = - mvf ;
                  l = mvs + mvf ;
                  scor = scor + penalty + ( penalty * ( l - 1) * pen_ext) ;
                  sank_pt [sp2][sp1].score_sh_str[ d ] = scor ;
                  }
              } // lup sp b
            }
            else
            {
             for (c=  0; c < nuspecs ; c ++ )
               sank_pt [c][sp1].score_sh_str[d] = -99999 ;}
          }
         }


 /* ACA CALCULO EL PROMEDIO ENTRE LAS DOS TRANSFORMACIONES ASI LOS COSTOS SON SIMETRICOS*/
for (a = 0 ; a < nuspecs ; a ++)
 for (b = a ; b < nuspecs ; b ++)
   {
   if (a == b) continue ;
  // printf("\nESPECIES A B %i %i------------------------------------",a,b);
   for (d = 0 ; d < dde ; d ++){
    i = translator_sh_str [0][d]; j = translator_sh_str [1][d] ;
    if (sank_mtx[a][b].score_sh_str [d] ==  -99999)
      {
      for (w= 0 ; w < dde ; w++){
        if ( ( translator_sh_str [0][w] == - i ) && ( translator_sh_str [1][w] == -j )){
         if (sank_mtx[b][a].score_sh_str [w] !=  -99999)
           sank_mtx[a][b].score_sh_str [d] = sank_mtx[b][a].score_sh_str [w] ;}}
      }
     else
      for (w= 0 ; w < dde ; w++)
      {
        if ( ( translator_sh_str [0][w] == - i ) && ( translator_sh_str [1][w] == -j )) {
         if (sank_mtx[b][a].score_sh_str [w] ==  -99999){
           sank_mtx[b][a].score_sh_str [w] = sank_mtx[a][b].score_sh_str [d] ;}
         else{
            score  = sank_mtx[b][a].score_sh_str [w] ;
            besco  = sank_mtx[a][b].score_sh_str [d] ;
            scor =  (score + besco) / 2 ;
            sank_mtx[b][a].score_sh_str [w] = scor ;
            sank_mtx[a][b].score_sh_str [d] = scor ;
            }
           }
           }
        }
    }

for ( a = 0; a < nuspecs ; a++)
  {
  for ( b = 0; b < nuspecs ; b++)
     {

       if ( a == b ){
       //  printf ("   -     " ) ;
            continue ;}
       besco = 99999999;

       for (i = 0 ; i <  dde   ; i ++ )
          {
           if ( (sank_mtx[a][b].score_sh_str[ i ]  < besco) && (sank_mtx[a][b].score_sh_str[ i ] != -99999) )
            {
             besco = sank_mtx[a][b].score_sh_str[ i ] ;
             w_besco = i ;
            }
           }
       sank_mtx[a][b].best_sh_str = w_besco ;
     }
  }

}//make_shift_stretchs_recat


int accept_sh_str(int i,int j ){
int  span1,span2 ;

      if ((i == 0) || (j==0 )  || (j==i))
        return (0) ;
       //   ACA ME FIJO CUANTAS CATEGS DE LA SP MODIFICADA QUEDAN
       span1 =  NUCATEG - i + j ;
       span2 =  NUCATEG ;
       if ( span1 < MINCATS ) {
          // printf("\n%i/%i RECHAZADO POR una traject muy corta en la sp modificada categs ",i,j) ;
           return (0) ;}
       // ESTOS SON SOBRE EXTENSION DE UNO SOBRE EL OTRO
       if (  span2 > span1)
        if (span2/span1 >= 3 ){
          return (0) ;}
        else
         if ( span1/span2 >= 3 )
           { 
                return (0) ;
            }
    return (1) ;
}

void make_stretch_inv (sp1,sp2,nucateg,especies) {// cuando el stretch_inv es negativo se alarga para la izquier.da (mas largo q la ancestral)
int  i,       dde = 0  , categ,w_besco, cat, move ;
Punktyp * pt_sp1, * pt_sp2 ;
double besco,dist_start,dist_end, score  ;
        // printf("STRETCHS_inv\n") ;
              for (i = - ( nucateg - 2 ) ; i < ( nucateg - 1)  ; i ++ ){
                  if ( i == 0 ) continue ;
                  translator_strinv [dde] = i ;
                  categ = nucateg - 1 ;
                  pt_sp1 = consense_matrix [sp1][categ].pt ; //define q celda de la sp 1 en comiezo cdo corro sp2 a la izq
                  pt_sp2 = consense_matrix [sp2][categ].pt ; //define q celda de la sp 2 en comiezo cdo corro sp2 a la izq
                  dist_end= pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                  if (i > 0 )
                    {
                     categ = cat =   i ;  ;
                     pt_sp1 = consense_matrix [sp1][categ].pt ; //define q celda de la sp 1 en final cdo corro sp2 a la izq
                     categ =    0 ;
                     pt_sp2 = consense_matrix [sp2][categ].pt ; //define q celda de la sp 2 en final cdo corro sp2 a la izq
                  
                     } else {
                      categ = cat= 0 ;
                      pt_sp1 = consense_matrix [ sp1][categ ].pt ; //define q celda de la sp 1 en final cdo corro sp2 a la der
                      categ =  - i;
                      pt_sp2 = consense_matrix [ sp2][categ ].pt ; //define q celda de la sp 2 en final cdo corro sp2 a la der
                    
                      }
                    if (i <  0 )
                      move = -i ;
                     else
                      move =  i;
                   dist_start = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                   score = (dist_start + dist_end )/ 2  ;
                   score = score + penalty + (penalty * ( move - 1) * pen_ext) ;
                   sank_mtx[sp1][sp2].score_str_inv[ dde ] = score + (penalty * move ) ;// sank_mtx[sp1][sp2].score_str_inv[ dde ] = score + penalty  ;//MORELO
               
                   dde ++;
                   }


jumany_str = dde ; 
besco = 10000000 ;
       for (i = 0 ; i <  dde   ; i ++ ){
           if ( (sank_mtx[sp1][sp2].score_str_inv[ i ]  < besco)  && (sank_mtx[sp1][sp2].score_str_inv[ i ]  != -99999 ))
            {
              besco = sank_mtx[sp1][sp2].score_str_inv[ i ] ;
              w_besco = i ;}
           }
           sank_mtx[sp1][sp2].best_stri = w_besco ;
}//make_stretch_inv


void make_sh_str (sp1,sp2,nucateg,especies) { //cuando el stretch es negativo se acorta  para la izquierda el desce (queda igual el anc)
int  i,j,l,k  , span1,span2, dde = 0  , w_besco, cat,move_sh, move_str,categ_sp1_star, categ_sp2_star,categ_sp1_fin, categ_sp2_fin;
Punktyp * pt_sp1, * pt_sp2 ;
double besco,dist_start,dist_end, score  ;
transo = 0 ;
       for (i = - ( nucateg - 3 ) ; i < ( nucateg - 2)  ; i ++ ){
                  if ( i == 0 ) continue ;
                     if (i < 0 )
                      {
                       categ_sp1_star = 0 ;
                       pt_sp1 = consense_matrix [sp1][categ_sp1_star].pt ; //define q celda de la sp 1 en comiezo cdo corro sp2 a la izq
                       categ_sp2_star =   ( - i )  ;
                       pt_sp2 = consense_matrix [sp2][categ_sp2_star].pt ; //define q celda de la sp 2 en comiezo cdo corro sp2 a la izq
                    
                       dist_start= pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                      }
                       else
                       {
                        categ_sp1_star =   i ;
                        pt_sp1 = consense_matrix [sp1][categ_sp1_star].pt ; //define q celda de la sp 1 en comiezo cdo corro sp2 a la der
                        categ_sp2_star =  0 ;
                        pt_sp2 = consense_matrix [sp2][categ_sp2_star].pt ; //define q celda de la sp 2 en comiezo cdo corro sp2 a la der
                        dist_start= pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                     
                       }
                      if (i <  0 )
                       move_sh = -i ;
                     else
                       move_sh =  i;
                      for (j =   - ( nucateg - 1 )   ; j < ( nucateg - 1)   ; j ++ )
                      {
                       if (j==0 ) continue ;
                       if (j==i) continue ;
                       if (j < 0 ) {
                          categ_sp1_fin = cat =   ( nucateg  - 1 ) + j ;  ;
                          categ_sp2_fin =         (  nucateg - 1 ) ;
                          span1 =  categ_sp1_fin - categ_sp1_star - 1 ;
                          span2 =  categ_sp2_fin - categ_sp2_star - 1 ;
                          if ( span1 < 1 )  continue ;
                          if ( span2 < 1   )  continue ;
                          if (  span2 > span1)
                            if (span2/span1 > 4 ) continue ;
                          else
                            if ( span1/span2 > 4 ) continue ;
                           pt_sp1 = consense_matrix [sp1][categ_sp1_fin].pt ; //define q celda de la sp 1 en final cdo corro sp2 a la izq
                           pt_sp2 = consense_matrix [sp2][categ_sp2_fin].pt ; //define q celda de la sp 2 en final cdo corro sp2 a la izq
                           dist_end= pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                    
                          }
                      else{// j > 0
                           categ_sp1_fin = cat= ( nucateg - 1 ) ;
                           categ_sp2_fin =   ( nucateg - 1 ) - j;
                           span1 =  categ_sp1_fin - categ_sp1_star - 1 ;
                           span2 =  categ_sp2_fin - categ_sp2_star - 1 ;
                           if ( span1 < 1 )  continue ;
                           if ( span2 < 1 )  continue ;
                           if (  span2 > span1)
                            if (span2/span1 > 4 ) continue ;
                           else
                            if ( span1/span2 > 4 ) continue ;
                           pt_sp1 = consense_matrix [ sp1 ][categ_sp1_fin].pt ; //define q celda de la sp 1 en final cdo corro sp2 a la der
                           pt_sp2 = consense_matrix [ sp2 ][categ_sp2_fin ].pt ; //define q celda de la sp 2 en final cdo corro sp2 a la der
                           dist_end= pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                       

                            }
                       score = (dist_start + dist_end) / 2;
                       if (j <  0 )
                         move_str = -j ;
                       else
                         move_str =  j;
                       if (move_str >= move_sh )
                        { k = move_str ;
                          l = k + ( move_str - move_sh); }
                       if (move_sh > move_str ){ k = move_sh ;  l = k + ( move_sh - move_str);}
                       score = score + penalty + ( penalty * ( l - 1) * pen_ext) ;
                       sank_mtx[sp1][sp2].score_sh_str[ dde ] = score + (penalty * move_sh ) + (penalty * move_str ); 
                

                       if (!transo){
                       translator_sh_str [0][dde] = i ;
                       translator_sh_str [1][dde] = j ;}
                       dde ++;

                      }

                  }

if (transo == 0 )
   transo = dde ;

jumany_str = dde ;
if (jumany_str == 0 )
  {
  sank_mtx[sp1][sp2].score_sh_str[ 0 ] = 99999999999 ;
  sank_mtx[sp1][sp2].best_sh_str = 0 ;
  }
  else
   {
   besco = 10000000 ;
   for (i = 1 ; i <  transo   ; i ++ ){
      if ( (sank_mtx[sp1][sp2].score_sh_str[ i ]  < besco)  && (sank_mtx[sp1][sp2].score_sh_str[ i ]  != -99999 ))
       {
         besco = sank_mtx[sp1][sp2].score_sh_str[ i ] ;
         w_besco = i ;}
        }
        sank_mtx[sp1][sp2].best_sh_str = w_besco ;}

}//make_d_rest


void make_str_sh (sp1,sp2,nucateg,especies) { //cuando el  es negativo se acorta  para la izquierda el desce (queda igual el anc)
int  i,j  ,   dde = 0  , w_besco, cat,move_sh, move_str,categ_sp1_star, categ_sp2_star,categ_sp1_fin, categ_sp2_fin;
Punktyp * pt_sp1, * pt_sp2 ;
double besco,dist_start,dist_end, score  ;
  /* printf("\n-----------\n") ;
      printf("str_sh sps %i,%i",sp1,sp2) ; */
              for (i = 1 ; i < ( nucateg - 2)  ; i ++ ){

                  if ( i == 0 ) continue ;
                      categ_sp1_star =   i ;
                      pt_sp1 = consense_matrix [sp1][categ_sp1_star].pt ; //define q celda de la sp 1 en comiezo cdo corro sp2 a la der
                      categ_sp2_star =  0 ;
                      pt_sp2 = consense_matrix [sp2][categ_sp2_star].pt ; //define q celda de la sp 2 en comiezo cdo corro sp2 a la der
                      dist_start= pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                     if (i <  0 )
                       move_sh = -i ;
                     else
                       move_sh =  i;
                      for (j = - ( nucateg - 2 ) ; j < ( nucateg - 1)  ; j ++ )
                      {
                       if (j==0 ) continue ;
                       if (j==i ) continue ;
                       if (j < 0 ) {
                          categ_sp1_fin = cat =   ( nucateg- 1 ) + j ;  ;
                          categ_sp2_fin =    ( nucateg- 1 ) ;
                          if ( (categ_sp1_fin - categ_sp1_star ) < 2 ) continue ;
                          if ( (categ_sp2_fin - categ_sp2_star) < 2  )  continue ;
                          pt_sp1 = consense_matrix [sp1][categ_sp1_fin].pt ; //define q celda de la sp 1 en final cdo corro sp2 a la izq
                          pt_sp2 = consense_matrix [sp2][categ_sp2_fin].pt ; //define q celda de la sp 2 en final cdo corro sp2 a la izq
                          dist_end= pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                           }
                      else{// j > 0
                           categ_sp1_fin = cat= ( nucateg - 1 ) ;
                           categ_sp2_fin =   ( nucateg - 1 ) - j;
                           if ( (categ_sp1_fin - categ_sp1_star ) < 2 ) continue ;
                           if ( (categ_sp2_fin - categ_sp2_star) < 2  )  continue ;
                           pt_sp1 = consense_matrix [ sp1 ][categ_sp1_fin].pt ; //define q celda de la sp 1 en final cdo corro sp2 a la der
                           pt_sp2 = consense_matrix [ sp2 ][categ_sp2_fin ].pt ; //define q celda de la sp 2 en final cdo corro sp2 a la der
                           dist_end= pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                   

                            }
                      if (j <  0 )
                         move_str = -j ;
                       else
                         move_str =  j;
                       score = dist_start + dist_end ;
                       sank_mtx[sp1][sp2].score_str_sh[ dde ] = score + (penalty * move_sh ) + (penalty * move_str );
                   
                       translator_str_sh [0][dde] = i ;
                       translator_str_sh [1][dde] = j ;
                       dde ++;
                      }

                  }


jumany_str = dde ;
besco = 10000000 ;
       for (i = 1 ; i <  dde   ; i ++ ){
           if ( (sank_mtx[sp1][sp2].score_str_sh[ i ]  < besco)  && (sank_mtx[sp1][sp2].score_str_sh[ i ]  != -99999 ))
            {
              besco = sank_mtx[sp1][sp2].score_str_sh[ i ] ;
              w_besco = i ;}
           }
           sank_mtx[sp1][sp2].best_str_sh = w_besco ;
}//make_str_sh

int read_data () {
    int i, a=0,ctos  ;
     char   buffer [5000] ;
     char * pt_char,stri[100] ;
     contlin = 0 ;
        while (1)
           {
            i =  read_next_line ( buffer) ;
            if ( !i )
               break ;
             pt_char = buffer  ;
            ctos = borrar_espacios(pt_char) ;
            pt_char += ctos ;
            if (isdigit (* pt_char) || ( * pt_char == '-')  ){
              printf ("\nError! Line \"LM=\" not found (line %i)",contlin);
             return (0); }
             for(i = 0; i<100; i++)
               stri[i] = tolower(buffer[i]); 
             //if (( strstr(buffer,"LM=" ) != NULL ) || ( strstr(buffer,"LM3=" ) != NULL )) {  //FLAG
            if (( strstr(stri,"lm=" ) != NULL ) || ( strstr(stri,"lm3=" ) != NULL )) {  //FLAG
                if (save_configuration ( a, DIMS, LANDS, buffer ) )
                   printf("");
                 else{
                  printf ("\n Error reading the data at line %i ", contlin);
                  return (0) ; }
                  }
           a ++ ;
           }
           nuconfs = a ;
           nuspecs =  count_species ( nuconfs ) ;
           if (nuspecs < 4 ){
            printf ("\n Error: less than four species in dataset ");
            fflush(stdout) ;
                  return (0) ;}
    return (1);
}// read_data

int read_tmp_data (int allcateg,int asis) { // cuando es recat el tmp_data lee de TNT las configs ancestrales y las en optimus matrix guarda ordenadas como en el alineamiento es decir mantiene las posic.
                                             // cuando es shift (discreto) lo que hace es guardar todo en una matriz sin dejar espacios para los gaps.
    int i, a=0 ,l,b ;
     char   buffer_tmp [10000] ;
     if (asis)
       input_file = fopen ("asis_2pasos.tmp","rb") ; // abre el archivo con las coordenadas ancestrales
     else
       input_file = fopen ("chg_2pasos.tmp","rb") ; // abre el archivo con las coordenadas ancestrales
  for (a = 0 ; a < 199 ; a ++)
     where [a] = 0 ;
  for (a = 0 ; a < nuspecs ; a ++) // esto lo tengo qeu cambiar para los que son recat !!! xq el numero de categs de los terminales too cambia.
   for (b = 0 ; b < NUCATEG ; b ++)
     for (l = 0 ; l < LANDS ; l ++){
        optimus_matrix [a][b].pt[l].x = consense_matrix[a][b].pt[l].x ;
        optimus_matrix [a][b].pt[l].y = consense_matrix[a][b].pt[l].y ;
        optimus_matrix [a][b].pt[l].z = consense_matrix[a][b].pt[l].z ;}
  for (a = 0 ; a < allcateg ; a ++)
           {
            i =  read_next_line ( buffer_tmp) ;
            if ( !i )
             break ;
            if ( strstr(buffer_tmp,"TOTAL" ) != NULL ){
                if (save_configuration_tnt ( a ,  buffer_tmp,asis ) )
                   printf("");
                 else{
                  printf ("\n Error reading the data at line %i ", contlin);
                  return (0) ; }
                  }

           }

  remove ("chg_2pasos.tmp");
  fclose (input_file) ;

   return (1);
}// read_tmp_data



int save_configuration_tnt ( int stage,char * biffer, int asis){

 int l = 0,  ctos,s, nodo ;
 double uno , dos,  tres ;
 char    * pt_char ;
 Punktyp * pt ;

for (s= nuspecs; s <  ((2 *nuspecs) -1) ; s++){ // uso t2p xq el orden lo da el archivo q esta leyendo
    nodo = nod_t2p [ s] ;
   read_next_line ( biffer) ;
   if (asis)
      pt = optimus_matrix [nodo][ stage].pt ;  //ACA TENGO QUE SOLO GUARDAR LAS CATEGORIAS QUE SON LAS DE CADA NODO.
   else
    {
    if (!mask_aln [nodo][stage] )
      continue ;
    pt = optimus_matrix [nodo][ where[nodo] ].pt ;}  //ACA TENGO QUE SOLO GUARDAR LAS CATEGORIAS QUE SON LAS DE CADA NODO.
    pt_char = biffer  ;
    while (!isspace (* pt_char)  ){
      pt_char ++ ;  }
    for (l = 0 ; l < LANDS ; l++){
          ctos = borrar_espacios(pt_char) ;
          pt_char += ctos ;
         if ((isdigit ( pt_char)) ||( *pt_char != '-')|| (  *pt_char != '+') )
             {
              if (DIMS == 2){
              sscanf ( pt_char,"%lG",&uno) ;
              pt_char = strchr( pt_char,',');
              pt_char ++ ;
              sscanf ( pt_char,"%lG",&dos) ;
              pt->x= uno ; pt->y = dos;
              pt_char = strchr( pt_char,' ');
              pt_char ++ ;
             }
             else{
              sscanf ( pt_char,"%lG",&uno) ;
               pt_char = strchr( pt_char,',');
              pt_char ++ ;
              sscanf ( pt_char,"%lG",&dos) ;
              pt_char = strchr( pt_char,',');
              pt_char ++ ;
              sscanf ( pt_char,"%lG",&tres) ;
              pt->x= uno ; pt->y = dos; pt->z = tres ;
              pt_char = strchr( pt_char,' ');
              }
              }
           else{
              printf ("Error! Configuration %i has less than %i lands (line %i)",stage,LANDS,contlin);
              return (0);}
           pt ++ ;
           }
           where [ nodo ] ++ ;
           }


     return (1) ;
 }// save_configuration_tnt

int save_configuration_tnt_recat ( int stage,char * biffer, int asis){

 int l = 0,  ctos,s, nodo ;
 double uno , dos,  tres ;
 char      * pt_char  ;
 Punktyp * pt ;

for (s= nuspecs; s <  ((2 *nuspecs) -1) ; s++){ // uso t2p xq el orden lo da el archivo q esta leyendo
    nodo = nod_t2p [ s] ;
   read_next_line ( biffer) ;
   if (!mask_aln [nodo][stage] )
      continue ;
    pt = optimus_matrix [nodo][ stage ].pt ;
    pt_char = biffer  ;
    while (!isspace (* pt_char)  ){
      pt_char ++ ;  }
    for (l = 0 ; l < LANDS ; l++){
          ctos = borrar_espacios(pt_char) ;
          pt_char += ctos ;
         if ((isdigit ( pt_char)) ||( *pt_char != '-')|| (  *pt_char != '+') )
             {
              if (DIMS == 2){
              sscanf ( pt_char,"%lG",&uno) ;
              pt_char = strchr( pt_char,',');
              pt_char ++ ;
              sscanf ( pt_char,"%lG",&dos) ;
              pt->x= uno ; pt->y = dos;
              pt_char = strchr( pt_char,' ');
              pt_char ++ ;
             }
             else{
              sscanf ( pt_char,"%lG",&uno) ;
               pt_char = strchr( pt_char,',');
              pt_char ++ ;
              sscanf ( pt_char,"%lG",&dos) ;
              pt_char = strchr( pt_char,',');
              pt_char ++ ;
              sscanf ( pt_char,"%lG",&tres) ;
              pt->x= uno ; pt->y = dos; pt->z = tres ;
              pt_char = strchr( pt_char,' ');
              }
              }
           else{
              printf ("Error! Configuration %i has less than %i lands (line %i)",stage,LANDS,contlin);
              return (0);}
         pt ++ ;
     }
 }


     return (1) ;
 }// save_configuration_tnt_recat


int generate_nodtrans ( ){
int uno,dos,a, caca ;

char nada [200] ;
char   bffer [10000] ;
for (a = 0 ; a < nuspecs ; a ++ ){
    nod_t2p[a] = a ;
    nod_p2t[a] = a ;}

for (a = 0 ; a < nuspecs-1 ; a ++ ){
    if (a == 0){
      read_next_line ( bffer) ;
      caca = sscanf ( bffer,"%i %i}",&uno,&dos) ;}
     else{
      read_next_line ( bffer) ;
      caca = sscanf ( bffer,"%i%s%i}",&uno,&nada,&dos) ;}
  nod_t2p [dos] = uno ;
  nod_p2t [uno] = dos ;
  }
 // nodtrans[dos] = uno ;
}


void dealloc_datamatrix ( int configs ) {
 int   h;
 for ( h = 0;  h < configs ; h++ )
      free ( datamatrix[ h ].pt );
 free ( datamatrix ) ;
}

void alloc_consense_matrix (int nuno, int categs, int nuland  ) {
 int  i, h ;
 consense_matrix = malloc ( nuno * categs * sizeof(Conftyp *) ) ;
 for (h = 0; h < nuno  ; h++ ){
     consense_matrix[h] = malloc (categs * sizeof (Conftyp ));
       for ( i = 0 ; i < categs; i ++) {
          consense_matrix [ h ][ i ].pt = (Punktyp *) malloc ( nuland * sizeof(Punktyp)) ;} }

 }
void alloc_optimus_matrix (int stados, int categs, int nuland  ) {
 int  i, h ;
 optimus_matrix = malloc ( stados * categs * sizeof(Conftyp *) ) ;
 for (h = 0; h < stados  ; h++ ){
     optimus_matrix[h] = malloc (categs * sizeof (Conftyp ));
       for ( i = 0 ; i < categs; i ++) {
          optimus_matrix [ h ][ i ].pt = (Punktyp *) malloc ( nuland * sizeof(Punktyp)) ;} }

 }


void alloc_buff_traj(int nucateg) {
 int a,i ;
 buff_traj = (Conftyp**) malloc ( 4 * nucateg * sizeof(Conftyp*) ) ;
 for (i=0; i < 5; i ++){
   buff_traj[i] = (Conftyp*) malloc ( nucateg * sizeof(Conftyp)) ;
   for (a=0; a < nucateg; a ++)
    buff_traj[i][a].pt =  (Punktyp *) malloc ( LANDS *   sizeof(Punktyp)) ;}
 bes_traj = malloc (  nucateg * sizeof(Conftyp) ) ;
 for (i=0; i < nucateg; i ++)
   bes_traj[i].pt =  (Punktyp *) malloc ( LANDS *   sizeof(Punktyp)) ;
}


void alloc_branch_labels (){
 int i ;
 branch_labels = malloc ( (2 * nt) * sizeof(char*) ) ;
 cats_labels = malloc   ( (2 * nt) * sizeof(char*) ) ;
 for (i = 0; i < ( 2 * nt ); i ++){
   branch_labels[i]  = malloc ( 300 * sizeof(char) ) ;
   cats_labels[i]  = malloc ( 300 * sizeof(char) ) ;  }
}

void dealloc_branch_labels (){
 int i ;
for (i = 0; i < ( 2 * nt ); i ++){
   free (branch_labels[i]) ;
   free (cats_labels [i]);}
 free (branch_labels) ;
 free (cats_labels) ;
}


void alloc_sank_mtx (  ) {
int a ;
sank_mtx = (Sank_spcelltyp**) malloc ( STATES * sizeof (Sank_spcelltyp * ) ) ;
if (sank_mtx==NULL){
  printf("Error. No enough RAM memory");
    }
for (a = 0 ; a < STATES ; a ++ ){
    sank_mtx [ a ]  = (Sank_spcelltyp*) malloc ( STATES  *   sizeof(Sank_spcelltyp  )) ;
    if (sank_mtx[a] == NULL){
     printf("Error. No enough RAM memory");
     }
         }
}


void dealloc_sank_mtx () {
  int a ;
    for (a = 0 ; a <  STATES ; a ++ )
       free (sank_mtx [ a ])  ;
   free (sank_mtx ) ;
}


void alloc_downcosts (  ) {
int a ;   // ESPECIES PRIMERO ESTADOS DESPUES
downcosts = malloc ( nnods * sizeof (double * ) ) ;
for (a = 0 ; a < nnods ; a ++ )
   downcosts [ a ]  = malloc (  STATES *   sizeof (double    )) ;
}


void dealloc_downcosts ( ) {
  int a ;
    for (a = 0 ; a < nnods ; a ++ )
       free (downcosts [ a ])  ;
   free (downcosts ) ;
}

void put_best_score (int nucas) {
 int a, b  ;
 double beshi, bestre, besa,bestri,beshistr,bestrshi ;
 Sank_spcelltyp ** pt_sank ;
 pt_sank = sank_mtx ;
   for (a = 0 ; a < STATES ; a ++ ){
         for (b = 0 ; b < STATES ; b ++ ){
           if ( a == b ) continue  ;

           besa = 1000000000 ; beshi = 1000000000 ; bestre = 1000000000 ;
           bestri = 1000000000 ; beshistr = 1000000000 ; bestrshi = 10000000 ;
           if (doasis)
             besa   =   pt_sank[a][b].score_asis  ;
           if (doshift)
               beshi  =   pt_sank[a][b].score_shft    [pt_sank[a][b].best_shft] ;
          if (!extended){
             if (dostre)
               bestre =   pt_sank[a][b].score_str  [pt_sank[a][b].best_str] ;
             if (doinvstre)
              bestri =   pt_sank[a][b].score_str_inv [pt_sank[a][b].best_stri] ;
            if (doshstre)
                beshistr = pt_sank[a][b].score_sh_str  [pt_sank[a][b].best_sh_str] ;   }
           if (doasis)
            if ( ( besa <= beshi)  && ( besa <= bestre ) && ( besa <= bestri ) && ( besa <= beshistr )  && ( besa <= bestrshi ) ){
              pt_sank[a][b].best_overall = besa ;
              pt_sank[a][b].what_best = 0 ;} // 0 es as is
           if (doshift)
            if ( ( beshi < besa)  && ( beshi <= bestre ) && ( beshi <= bestri ) && ( beshi <= beshistr ) && ( beshi <= bestrshi )  ){
               pt_sank[a][b].best_overall = beshi ;
               pt_sank[a][b].what_best =  1 ; } //shift es uno
          if (dostre)
            if ( ( bestre <= beshi)  && ( bestre <= besa ) && ( bestre <= bestri ) && ( bestre <= beshistr ) && ( bestre <= bestrshi )  ){
                 pt_sank[a][b].best_overall = bestre ;
                 pt_sank[a][b].what_best =  2 ; } //stretch es 2
          if (doinvstre)
             if ( ( bestri <= beshi)  && (  bestri  <= bestre ) && (  bestri  <= besa ) && (  bestri  <= beshistr ) && (  bestri  <= bestrshi )  ){
                   pt_sank[a][b].best_overall = bestri ;
                   pt_sank[a][b].what_best =  3 ; } //stretch_inv es 3
           if (doshstre)
              if ( ( beshistr <= beshi)  && (  beshistr  <= bestre ) && ( beshistr  <= bestri ) && (  beshistr  <= besa )   ){
                 pt_sank[a][b].best_overall = beshistr ;
                 pt_sank[a][b].what_best =  4 ; } //shi_stre es 4
   }
 }
}



void test_sank_mtx () {
 int a, b  ;
 Sank_spcelltyp ** pt_sank ;
 double maxval = -99999 ;
 double  piso, techo, factor ;
 pt_sank = sank_mtx ;
 sank_file= fopen("sankoff.out", "w");
    for (a = 0 ; a < STATES ; a ++ ){
      for (b = 0 ; b < STATES ; b ++ ){
        if ( a == b ) continue  ;
          if (pt_sank[a][b].best_overall > maxval)  
             maxval = pt_sank[a][b].best_overall ; }}

           factor = 999/maxval ; 
        for (a = 0 ; a < STATES ; a ++ ){
         for (b = 0 ; b < STATES ; b ++ ){
          if ( a == b ) continue  ;
            pt_sank[a][b].best_overall = pt_sank[a][b].best_overall * factor; }}
fclose(sank_file);

for (a = 0 ; a < STATES ; a ++ ){
      for (b = 0 ; b < STATES ; b ++ ){
        if ( a == b ) continue  ;
         piso  = floor(pt_sank[a][b].best_overall) ;
         techo = ceil (pt_sank[a][b].best_overall) ;
         if ((techo - pt_sank[a][b].best_overall ) <= (piso - pt_sank[a][b].best_overall ))
           pt_sank[a][b].best_overall =  techo;
         else
           pt_sank[a][b].best_overall = piso ; }}


  for (b = 0 ; b < STATES ; b ++ )
    for (a = 0 ; a < STATES ; a ++ ){
      if ( a != b )
        fprintf(sank_file," %i > %i %.0f ",a,b,pt_sank[a][b].best_overall) ; }

triangle_ineq () ;
fclose(sank_file);

sank_file= fopen("sankoff.out", "a");
fprintf(sank_file,"\n");
  for (b = 0 ; b < STATES ; b ++ )
    for (a = 0 ; a < STATES ; a ++ ){
      if ( a != b )
        fprintf(sank_file," %i > %i %.0f ",a,b,pt_sank[a][b].best_overall) ; }

 fclose(sank_file);
}
            
int define_dimensions ()
{
    int i,  paso = 0 ,ctos,j  ;
    char   bafer [5000] , *pt_char, stri[100] ;
    double uno , dos , tres ;
    pt_char = bafer  ;
    CONFS= 0 ; DIMS=  0; LANDS=0 ;
        while (1)
           {
            i =  read_next_line ( bafer) ;
            if ( !i )
             break ;
             for(j = 0; j<100; j++)
                stri[j] = tolower(bafer[j]); 
           if ( ( strstr(stri,"lm=" )!= NULL ) || ( strstr(stri,"lm3=" )!= NULL )  ){
          //  if ( ( strstr(bafer,"LM=" )!= NULL ) || ( strstr(bafer,"LM3=" )!= NULL )  ){
                if ( ! paso ){
                  pt_char= strchr (bafer,'=') ;
                  pt_char ++ ;
                  ctos = borrar_espacios(pt_char) ;
                  pt_char += ctos ;
                  LANDS = atoi ( pt_char) ;
                  i =  read_next_line ( bafer) ;
                  if (!i)
                   break ;
                  else
                   DIMS = sscanf ( bafer,"%lG%lG%lG",&uno,&dos,&tres) ;
                  if (DIMS==0)
                   return (0) ;

                  paso = 1 ;  }
                CONFS ++ ;
                }
          }
if (LANDS == 0 )
  return (0) ;
if (DIMS == 0 )
  return (0) ;
return (1) ;

}


void generate_sank_mtx () {
 int a, b,i  ;
 Sank_spcelltyp ** pt_sank ;
 char estados [32];
 char nombresk [300 ] ;
 pt_sank = sank_mtx ;
 
nombresk[0] = NULL;
if (STATES > 32){
  printf("\nWarning. Sankoff file not generated. TNT can analyze characters with up to 32 states (%i states in current dataset",STATES);
  return ;  }
   
strcat (nombresk,prefix) ;
strcat (nombresk,"_sankmtx.tnt")  ;
sank_file= fopen(nombresk, "w");
fprintf(sank_file,"\nnstates 32 ; \nxread \n %i %i",1,STATES);
i = 97 ; 
for (a = 0 ; a < STATES ; a ++ ) 
 if (a < 10 ) {
   estados [a] = a + '0' ;}
 else {    
   estados [ a ] = i + '0' ; 
   i ++ ;} 
for (a = 0  ; a < nuspecs ; a ++ )
  fprintf(sank_file,"\n%s %c ",sps_list[ a].sps_name,estados[a]);
fprintf(sank_file,"\n;\n ") ;
fprintf(sank_file,"cc ( 0 ; \n;") ;
fprintf(sank_file,"costs 0= "); 
  for (b = 0 ; b < STATES ; b ++ )
    for (a = 0 ; a < STATES ; a ++ ){
      if ( a != b )
        fprintf(sank_file," %c > %c %.0f  ",estados[a],estados[b],pt_sank[a][b].best_overall) ; }
  fprintf(sank_file,"; ");      
fclose(sank_file);

}

double sank_downpass ()
{
int  t , e, d , n, nodo   ;

double costo = 0, minescor=99999999999;


for ( n = 0 ; n < intnods ; n ++){
  nodo = optlist [n] ;
  for ( e = 0 ; e < STATES ; e ++)
    downcosts [ nodo ] [ e ] = 0 ; }


for (t= 0 ; t < nuspecs ; t ++ ) {
   for (e= 0 ; e < STATES ; e ++ ) {
       if (t  != e )
        downcosts [ t ] [ e ] = INFINIT;
       else
          downcosts [ t ] [ e ] = 0 ; }}

for ( n = 0 ; n < intnods ; n ++)
    {
     nodo = optlist [n] ;
     for ( e = 0 ; e < STATES ; e ++)
       {
        costo = 0 ;
        for (d = firs[nodo] ; d != - 9  ; d = sis [ d  ] )
           downcosts[nodo][e] += mincost ( d, e  ) ;
       }

     }


for ( n = 0 ; n < STATES ; n ++)
    if(downcosts[nt][n] < minescor)
     minescor = downcosts[nt][n] ;

return(minescor);
}


double mincost(int des, int guichstate ){
 int e ;
 double costo , mincosto = 9999999999 ;

if (opt_asis){
 for (e = 0 ; e < STATES ; e ++){
       costo =  sank_mtx[ e ][ guichstate ].score_asis  + downcosts [des][e] ;
       if (costo <  mincosto )
           mincosto = costo ; }}
else{
  for (e = 0 ; e < STATES ; e ++){
       costo =  sank_mtx[ guichstate ][ e ].best_overall  + downcosts [des][e] ;  //VERRRRRRRRR  costo =  sank_mtx[ e ][ guichstate ].best_overall  + downcosts [des][e] ;
       if (costo <  mincosto )
           mincosto = costo ; }}
 return (mincosto) ;
}



void sank_uppass ()
{
 int nodo, n,i,  dde, e  ;

for (n = 0 ; n < nnods ; n++)
  for (i = 0 ; i < 6 ; i ++ )
    all_trans [n][i] = 0 ;


for ( n = intnods  ;  n -- ; ){
 nodo = optlist [n] ;
 for (e = 0 ; e < STATES ; e ++)
   final_states [nodo][e] = -1 ;}

 for ( n = intnods  ;  n -- ; ){
       nodo = optlist [n] ;
       dde = 0 ;
      define_final_states ( nodo ) ;
           }
 for ( n = 0 ; n < nt  ;n ++)
     final_states[n][n] = 1 ;

complete_all_trans (); // esto es xq el lupeo de arriba no incluye terminales

}


void complete_all_trans (){
int f,i,nodo,cestro ;
 for (nodo= 0 ; nodo < nt ; nodo ++){
      cestro = ances [nodo ];
      for ( f = 0 ; f < STATES ; f ++)
         { //lupeo los estado optimos del ancestro
          if (final_states [ cestro ] [ f ] != -1)
           {
            mincosto [nodo ] = 99999999 ;
            i = sank_mtx[ f ] [ nodo ].what_best ;
            all_trans[nodo][i] ++;
           }
      }
 }  
}

void define_final_states ( nodo ) {
  int e,f ,cestro, s,   poli = 0 , i;
  double elcosto ;
  cestro = ances [nodo] ;
    if ( nodo == nt )
     {
     mincosto[nodo] = 999999999 ;
     for (e = 0 ; e < STATES ; e ++)
       {
        elcosto   = downcosts[nodo][e]  ;
        downcosts[nodo] [e] = truncate (elcosto)   ;
        if ( downcosts [ nodo ] [ e ]  <  mincosto [nodo] )
         mincosto [nodo] =  downcosts [ nodo ] [ e ]  ;
       }
       for (e = 0 ; e < STATES ; e ++){
         if (downcosts [ nodo ] [ e ]  == mincosto [ nodo ] )
          {
           final_states [nodo][e] = 1 ;
           poli ++ ;
          }
         }
     }
     else
      {
        for ( f = 0 ; f < STATES ; f ++)
         { //lupeo los estado optimos del ancestro
          if (final_states [ cestro ] [ f ] != -1)
           {
            mincosto [nodo ] = 99999999 ;
            for ( e = 0 ; e < STATES ; e ++)
              { //lupeo todos los estados del nodo en cuestion
               if (opt_asis)
                elcosto   = downcosts[nodo][e] + sank_mtx [ f ] [ e  ].score_asis ;
               else
                elcosto   = downcosts[nodo][e] + sank_mtx [ f ] [ e  ].best_overall ;
               upcosts [e] = truncate (elcosto) ;
             if (  upcosts [e] < mincosto [ nodo] )
               mincosto  [nodo] = upcosts [e] ;
            }
            for ( s =  0 ; s < STATES ; s ++ )
             if (( upcosts [s] ) == mincosto [nodo] ){
              final_states [nodo][s] = 1  ;
              poli++ ;
              i = sank_mtx[ f ] [ s ].what_best ;
              all_trans[nodo][i] ++;
              }
           }
         }
      }
    if (poli > 1)
       ispoli [nodo] = 1 ;

}//end


void alloc_final_states ( ) {
 int n, e  ;
  final_states = malloc ( nnods * sizeof (int * ) ) ;
    for ( n =  0 ; n < nnods ; n ++)
       final_states [n] = malloc ( STATES *   sizeof (int    )) ;

  for  ( n= 0 ; n < nnods ; n ++)
    for  ( e= 0 ; e < STATES ; e ++)
     final_states [n] [e] = -1 ;

}

void dealloc_final_states ( ) {
 int a ;
    for (a = 0 ; a < nnods ; a ++ )
       free (final_states [ a ])  ;
   free (final_states ) ;
}

void alloc_upcosts ( ){

   upcosts = (double * ) malloc ( STATES * sizeof (double ) ) ;
}


void alloc_ispoli ( ){
  int i ;
 ispoli = ( int * ) malloc (nnods * sizeof (  int )  ) ;
 for (i= 0 ; i < nnods ; i ++)
     ispoli[i] = 0 ;

}


double fill_reconstructions_new (int nd ){
int  n, st_anc, e, nodo, st_nod , optstate ;
double mincore, score ;
if ( recons   == NULL)
  alloc_recons ( ) ;
for ( n = intnods  ;  n -- ; ){
 nodo = optlist [n] ;
 if (nodo == nt ){
  for (e = 0 ; e < STATES ; e ++)    //ACA TENGO QUE ELEGIR SIEMPRE EL MISMO Y SER CONSECUENTE EN TODO EL PROGRAMA
    if (final_states [nodo][e] == 1){
       recons[0][ nodo ] = e ; break;}}
  else {
    mincore = 999999 ;
    for (e = 0 ; e < STATES ; e ++){
      if (final_states [nodo][e] == 1)
      {
       st_anc = recons[ 0 ][ ances[nodo] ];
       if (opt_asis)
         score = downcosts[nodo][e] + sank_mtx [st_anc ] [e].score_asis ;
       else
         score = downcosts[nodo][e] + sank_mtx [st_anc ] [e].best_overall;
       if( score < mincore){
        mincore = score ;
        optstate = e ;}
      } }
      recons[0][nodo] = optstate ;
  }
}
recons[0][nt] = recons[0][OUTGRP] ;

  score =  0;
  for (n =  0 ; n < nnods ; n++ )
   {
   if (n == nt) continue;
    st_anc = recons[ 0 ][ ances [n] ];
    if ( n < nt )
      st_nod = n  ;
    else
      st_nod = recons[ 0 ][ n ];
    if (opt_asis)
     score += sank_mtx [st_anc ] [st_nod].score_asis;
    else
     score += sank_mtx [st_anc ] [st_nod].best_overall;
   }
   score = truncate (score ) ;


return (score);
}



void alloc_recons () {
int a ,c;
c= 1 ; //ojo aca deje lugar  para pocas recontrucciones.
recons =   malloc ( c  *   sizeof(int * )) ;
  for ( a = 0; a < c ; a++ )
      recons [ a ] =  malloc ( nnods *   sizeof(int)) ;

 opt_recons = ( int * ) malloc (totrecs * sizeof (  int )  ) ;
 for (a= 0 ; a < totrecs ;a ++)
     opt_recons[a] = 0 ;
}

void dealloc_recons (  ) {
  int a ;
    for (a = 0 ; a <  1 ; a ++ )
       free (recons [ a ])  ;
   free ( recons ) ;
   free (opt_recons) ;
   recons=NULL;
}

double truncate (double costo ){
int costin ;
double cost ;
    cost = (costo  * 100000) + 0.5 ;
    costin =  cost ;
    cost = (double) costin / 100000 ;
return (cost) ;
}



void define_limits_alignment_cont (  int guichsp){
int lims,   j  ,  van=0 ;
double span ;
lims = sup_limit [guichsp] - inf_limit [guichsp] + 1 ;
   span = ( sps_list[guichsp].max_age - sps_list[guichsp].min_age )  / ( lims - 1 );
   printf("\nLimites alineamiento Especie %i ",guichsp);
   for (j = inf_limit[guichsp] ; j < sup_limit [guichsp] + 1 ; j ++ ){
    limits_aln [guichsp][j] = sps_list[guichsp].min_age + (  span * van )  ;
    printf("%f ",limits_aln [guichsp][j]);
    van++;}



}



void alloc_alignment (int totcats, int nuspecs ){
int h,i ;
  align_matrix =  malloc ( nuspecs * sizeof(Conftyp *) ) ;
  for (h=0; h<nuspecs ; h++ ){
   align_matrix [ h ]  =  malloc ( totcats * sizeof(Conftyp)) ;
     for ( i = 0 ; i < totcats; i ++) {

          align_matrix [ h ][ i ].pt = (Punktyp *) malloc ( LANDS * sizeof(Punktyp)) ;}
  }
}



int sorting_confs_in_cats_alignment (int nucats, int guichsp ){
int  j , cual=0, k, especie ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_conf = datamatrix ;
pt_sp = sps_list ;
especie = guichsp ;
for (j = 0 ;  j <  nucats     ; j ++)
  yes_str [j] = 0   ;

for (j = 0 ;  j < pt_sp [ especie ].num_confs   ; j ++)
   pt_conf [ pt_sp [especie].conflist [j] ].which_aln_class = -1 ;


for (j = 0 ;  j < pt_sp [ especie ].num_confs  ; j ++)
        {
          cual = pt_sp [especie].conflist [j] ;
          for (k = 0 ;  k < nucats    ; k ++)
          {
           if ( k <  inf_limit [ guichsp ] || k > sup_limit [ guichsp ])
             continue ;
           if ( k == inf_limit [ guichsp ]  )
              {
               if ( ( pt_conf[cual].age >= limits_aln [especie][k] ) && (pt_conf[cual].age < limits_aln [especie][k+1] ) )
                 {
                  yes_str [k] = 1 ;
                  pt_conf[cual].which_aln_class = k ;
                 }
              }
             else
              if ( ( pt_conf[cual].age > limits_aln[especie][k] ) && (pt_conf[cual].age <= limits_aln[especie] [k+1] ) )
              {
               yes_str [k] = 1 ;
               pt_conf[cual].which_aln_class = k ;
              }

          }
        }


 for (j = 0 ;  j < nucats  ; j ++)
     if (j >=inf_limit || k > sup_limit [ guichsp ])
      continue ;
     if (yes_str [j] == 0 ){
      printf("\nAlignment  cannot be done given the lack of data");
      printf("\nNo obs for stage %i (%f-%f) species %i",j,limits_aln[especie][j],limits_aln[especie][j+1],especie);
      printf("\n") ;
   /*   return (0) ;*/
       }
     return (1);
} // sorting_confs_in_cats_aln




void fill_alignment_w_consense_doall(int guichsp,int totcats, int doall) {
int i, j ,  nulan, l,  son, k , sips ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_sp = sps_list ;
pt_conf = datamatrix ;
nulan = datamatrix[0].nulands ;
for (i = 0 ;  i < totcats   ; i ++)
   align_matrix[guichsp][i].pt[0].x = - 10000001 ;

if (!doall)  /* si solo hizo shifts los consensos se llenan aca sin problema es solo mover las categorias sin recalcular los consensos */
 {
  for (j= 0 ;  j <  totcats  ; j ++)
  {
   if (inf_limit [guichsp] == j ){
    for (k= 0 ;  k <  NUCATEG  ; k ++,j++)
     for (l = 0; l < nulan ; l ++ ){
      align_matrix[ guichsp ][ j ].pt[ l ].x  =consense_matrix [ guichsp ][ k ].pt [ l ].x ;
      align_matrix[ guichsp ][ j ].pt[ l ].y  =consense_matrix [ guichsp ][ k ].pt [ l ].y ;
      align_matrix[ guichsp ][ j ].pt[ l ].z  =consense_matrix [ guichsp ][ k ].pt [ l ].z ;}}}
  }
  else   // Si es doall y el tiempo es continuo aca genera un alineamiento.
    if (timeas) // si hizo shift y stretch pero es no categorical lo corre. No hace alineamiento si es categorical e hizo stretch.
     {
      define_limits_alignment_cont ( guichsp ); // las categorias dde se incluyen las configs son las totales del alineamiento
      sips =sorting_confs_in_cats_alignment ( totcats,  guichsp );
      for (j= 0 ;  j <  totcats  ; j ++)
        {
         for (l = 0 ; l < nulan ; l++){
         buff_dock[0].pt[l].x = 0;  buff_dock[0].pt[l].y = 0; buff_dock[0].pt[l].z = 0;
         }
         son = 0 ;
         for (i = 0 ;  i < pt_sp[guichsp].num_confs  ; i ++)
         {
          k = pt_sp[guichsp].conflist[i] ;
          if ( pt_conf [k].which_aln_class == j   ) {
           for (l = 0 ; l < nulan ; l++){
             buff_dock[0].pt[l].x  +=pt_conf[k].pt[l].x ;
             buff_dock[0].pt[l].y  +=pt_conf[k].pt[l].y;
             buff_dock[0].pt[l].z  +=pt_conf[k].pt[l].z;  }
           son ++ ;}
         }
         if ( son > 0 ) {
         for (l = 0 ; l < nulan ; l++){
          align_matrix[guichsp][j].pt[l].x = buff_dock[0].pt[l].x / son ;
          align_matrix[guichsp][j].pt[l].y = buff_dock[0].pt[l].y / son ;
          align_matrix[guichsp][j].pt[l].z = buff_dock[0].pt[l].z / son ;} }
 }
}

} //fill_aligned_matrix




void generate_output_file (int rec, char *type ) {
 sprintf(outputFilename, "%s",type);
 output_file= fopen(outputFilename, "w");
}

int my_spawn_hetero( )
{
    char jstr[(360*2)+256] ;

    char qqqstr[60]    ;


    STARTUPINFO startinfo;
    PROCESS_INFORMATION pinfo;
    DWORD how;
    how = 0;
    strcpy(qqqstr,"tnt ") ; //tiene que ir el nombre del archivo y el del script separado por ;
    strcat (qqqstr,outputFilename) ;
    strcat (qqqstr," chg_2tnt.tmp") ;



    startinfo.cb = sizeof(STARTUPINFO);
    startinfo.lpReserved = NULL;
    startinfo.lpDesktop = NULL;
    wsprintf(jstr,"RUNNING TNT");
    startinfo.lpTitle = jstr;
    startinfo.dwFlags = STARTF_USEPOSITION | STARTF_USESIZE ;
    startinfo.dwX = 50 ;
    startinfo.dwXSize = 700 ;
    startinfo.dwY = 100 ;
    startinfo.dwYSize = 250 ;
    startinfo.cbReserved2 = NULL;
    startinfo.wShowWindow = SW_SHOW;
       if(CreateProcess(NULL, qqqstr, NULL, NULL, FALSE ,
            HIGH_PRIORITY_CLASS | 0, NULL, NULL, &startinfo, &pinfo))
        WaitForSingleObject(pinfo.hProcess,INFINITE);
            else {
                MessageBox(hwnd,"TNT could not be started!","TNT executable should be is in the same folder than SPASOS",MB_OK | MB_ICONERROR );
                return(255);
            }
        GetExitCodeProcess(pinfo.hProcess, &how);
        return( how );
}

int my_spawn_asis( )
{
    char jstr[(360*2)+256] ;
     char qqstr[60] ="" ;
     STARTUPINFO startinfo;
    PROCESS_INFORMATION pinfo;
    DWORD how;
    strcpy(qqstr,"tnt ") ;
    strcat (qqstr,outputFilename) ;
    strcat(qqstr," asis_2tnt.tmp") ;

   ;

    startinfo.cb = sizeof(STARTUPINFO);
    startinfo.lpReserved = NULL;
    startinfo.lpDesktop = NULL;
    wsprintf(jstr,"RUNNING TNT");
    startinfo.lpTitle = jstr;
    startinfo.dwFlags = STARTF_USEPOSITION | STARTF_USESIZE ;
    startinfo.dwX = 50 ;
    startinfo.dwXSize = 700 ;
    startinfo.dwY = 100 ;
    startinfo.dwYSize = 250 ;
    startinfo.cbReserved2 = NULL;
    startinfo.wShowWindow = SW_SHOW;
       if(CreateProcess(NULL, qqstr, NULL, NULL, FALSE ,
            HIGH_PRIORITY_CLASS | 0, NULL, NULL, &startinfo, &pinfo))
        WaitForSingleObject(pinfo.hProcess,INFINITE);
            else {
                MessageBox(hwnd,"TNT could not be started!","TNT executable should be is in the same folder than SPASOS",MB_OK | MB_ICONERROR );
                return(255);
            }
        GetExitCodeProcess(pinfo.hProcess, &how);

        return( how );
}


int my_spawn_cont( )
{
    char jstr[(360*2)+256] ;
     char qqqstr[60]    ;


    STARTUPINFO startinfo;
    PROCESS_INFORMATION pinfo;
    DWORD how;
    how = 0;
    strcpy(qqqstr,"tnt ") ; //tiene que ir el nombre del archivo y el del script separado por ;
    strcat (qqqstr,outputFilename) ;
    strcat (qqqstr," ages.tmp") ;

    //strcpy(qqqstr,"tnt Hete_tmp ") ; //tiene que ir el nombre del archivo y el del script separado por ;
   ;

    startinfo.cb = sizeof(STARTUPINFO);
    startinfo.lpReserved = NULL;
    startinfo.lpDesktop = NULL;
    wsprintf(jstr,"RUNNING TNT");
    startinfo.lpTitle = jstr;
    startinfo.dwFlags = STARTF_USEPOSITION | STARTF_USESIZE ;
    startinfo.dwX = 50 ;
    startinfo.dwXSize = 700 ;
    startinfo.dwY = 100 ;
    startinfo.dwYSize = 250 ;
    startinfo.cbReserved2 = NULL;
    startinfo.wShowWindow = SW_SHOW;
       if(CreateProcess(NULL, qqqstr, NULL, NULL, FALSE ,
            HIGH_PRIORITY_CLASS | 0, NULL, NULL, &startinfo, &pinfo))
        WaitForSingleObject(pinfo.hProcess,INFINITE);
            else {
                MessageBox(hwnd,"TNT could not be started!","TNT executable should be is in the same folder than SPASOS",MB_OK | MB_ICONERROR );
                return(255);
            }
        GetExitCodeProcess(pinfo.hProcess, &how);
        return( how );
}



void fill_consense_matrix ( int espec, int nucats, int nuland  ){
int i, j ,k,  nulan, l,  son , a ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
Punktyp * conma ;
pt_conf = datamatrix ;
pt_sp = sps_list ;

nulan = datamatrix[0].nulands ;
for  ( a = 0 ; a < espec ; a ++ )
  {
    for (j= 0 ;  j < nucats  ; j ++)
    {
      conma = consense_matrix [ a ][ j ].pt;
      for (l = 0 ; l < nuland ; l++){
        conma->x = 0; conma->y = 0;conma->z = 0; conma++ ; }
      son = 0 ;
      for (i = 0 ;  i < pt_sp[ a ].num_confs  ; i ++)
       {
        k = pt_sp[ a ].conflist[ i ] ;
        if ( pt_conf [k].which_class == j ) {
         conma = consense_matrix [a][j].pt;
         for (l = 0 ; l < nuland ; l++){
            conma->x  +=pt_conf[k].pt[l].x ;
            conma->y  +=pt_conf[k].pt[l].y;
            conma->z  +=pt_conf[k].pt[l].z;
            conma++; }
         son ++ ;}
       }
      conma = consense_matrix [a][j].pt;
      for (l = 0 ; l < nuland ; l++){
          conma->x  =  conma->x  / son ;
          conma->y  =  conma->y  / son ;
          conma->z  =  conma->z  / son ; conma++ ;}
     }
 }



return ;

}  //fill_consense_matrix



void map_changes (int qreco, int resampling){

int n,  shift,stre,std_anc,std_nod,stra,stri, num, sign, sig ;
Sank_spcelltyp ** pt_sank ;
char etiqueta [50], numero [5], numerob[5];


numero [0] = NULL ;
numerob[0] = NULL;

pt_sank = sank_mtx ;
fflush(stdout);


 for (n =  0 ; n < nnods ; n++ )
 {
     etiqueta [0] = NULL;

 if (n == nt){
     itoa(n,numero,10);
     strcpy (etiqueta,numero) ;
     strcat (etiqueta,"_") ;
     strcpy (branch_labels[n],etiqueta);}
 else {

   std_anc = recons[ qreco ][ ances [n] ];
   if ( n < nt )
      std_nod = n  ;
   else
     std_nod = recons[ qreco ][ n ];
 
 if(opt_asis == 1 )
      itoa(n,numero,10);
 else {
   if ( pt_sank[std_anc][std_nod].what_best == 0 ){// 0 es as is
        if (resampling > 0){
          transform_rnd[n] [resampling-1] = 0 ;
         }
        else{
          transformations [n] = 0 ;
          branch_labels[n][0]= '\0' ;
         }
       }
   else
    if ( pt_sank[std_anc][std_nod].what_best == 1 ){//shift es uno
      if (resampling > 0)
          transform_rnd [n] [resampling-1] = 1 ;
      else
        transformations [n] = 1 ;
      strcat (etiqueta,"Shi_") ;
      shift=  pt_sank[std_anc][std_nod].best_shft ;
      shift = translator_sh [shift] ;
      if (resampling > 0)
          guich_rnd [n][resampling-1] = shift ;
      else {
          guich_map [n] = shift ;
          itoa(shift,numero,10);
          strcat(etiqueta,numero);
         strcpy (branch_labels[n],etiqueta);
     }
     }
    else
     if ( pt_sank[std_anc][std_nod].what_best == 2 ){// stre es dos
       if (resampling > 0)
          transform_rnd [n] [resampling-1] = 2 ;
        else
          transformations [n] = 2 ;
        itoa(std_nod,numero,10);
        strcat (etiqueta,"StrE_") ;
        stre=  pt_sank[std_anc][std_nod].best_str ;
        stre = translator_str [stre] ;
        if (resampling > 0 )
         guich_rnd [n][resampling-1] = stre ;
        else{
         guich_map [n] = stre ;
         itoa(stre,numero,10);
         strcat(etiqueta,numero);
         strcpy (branch_labels[n],etiqueta);
    
      }
        }
    else
     if ( pt_sank[std_anc][std_nod].what_best == 3 ){// streinv es dos
       if (resampling > 0)
          transform_rnd [n][resampling-1] = 3 ;
        else
         transformations [n] = 3 ;
         strcat (etiqueta,"StreS_") ;
        stre=  pt_sank[std_anc][std_nod].best_stri ;
        stre = translator_strinv [stre] ;
        if (resampling > 0 )
         guich_rnd [n][resampling-1] = stre ;
        else{
         guich_map [n]  = stre ;
         itoa(stre,numero,10);
         strcat(etiqueta,numero);
         strcpy (branch_labels[n],etiqueta);
   
      }
     }
    else
      if ( pt_sank[std_anc][std_nod].what_best == 4 ){
       if (resampling > 0)
          transform_rnd [n][resampling-1] = 4 ;
        else
         transformations [n] = 4 ;
        strcat (etiqueta,"Dstre") ;
        stri=  pt_sank[std_anc][std_nod].best_sh_str ;
        stre  = translator_sh_str [0][stri] ;
        stra  = translator_sh_str [1][stri] ;
        itoa(stre,numero,10);
        itoa(stra,numerob,10);
        if (stre < 0 ) {
           sign = 1000 ;
           stre = - stre ; }
          if (stra < 0 ){
           sig = 100 ;
           stra= - stra ; }
          stre = stre * 10 ;
          num = sign + sig + stra + stre ;
        if (resampling > 0){
          guich_rnd [n][resampling-1] = num ; }
         else {
          guich_map [n] = num ;
          strcat(etiqueta,numero);
          strcat(etiqueta,numerob);
          strcpy (branch_labels[n],etiqueta);
  
       }
      }/*
     else
      if ( pt_sank[std_anc][std_nod].what_best == 5 ){
       if (resampling)
          transform_rnd [n] = 5 ;
        else{
          transformations [n] = 5 ;
          strcpy (etiqueta,"StreSh_") ;
          stri=  pt_sank[std_anc][std_nod].best_str_sh ;
          stre  = translator_str_sh [0][stri] ;
          stra  = translator_str_sh [1][stri] ;
          itoa(stra,numerob,10);
          itoa(stre,numero,10);
          strcat(etiqueta,numerob);
          strcat(etiqueta,numero);
          strcpy (branch_labels[n],etiqueta);
          printf("\nRama %i-%i= %i -> %i, sh%i sh%i",ances [n],n,std_anc,std_nod,stra,stre);}
         } */
     }
   }
 }
}//map_changes


void check_ambiguity (){

int n ;
int i;

for (n=0 ; n < nnods ; n++)
    for (i = 0 ; i < 5 ; i++)
      if (bak_all_trans[n][i] != 0 )
          bak_all_trans[n][5] ++ ;
if (bak_all_trans[OUTGRP][5]){
  printf("\r                                                                                         ");   
  printf("\nWARNING: Ambiguity  inferred at the base of the tree. Change in developmental timing");
  printf("\n         assinged to one of the descending branches ");}
  printf("\nRunning the analysis...");            

}




void generate_alignment_asis (int nucateg,int nuspecs ){
int i,j,l;
Sptyp * pt_sp ;
Punktyp * pt_1 ;
pt_sp = sps_list ;
outputFilename[0] = NULL;
strcat (outputFilename,prefix) ;
strcat (outputFilename,"_aln.tnt") ;
strcpy (finalFilename,outputFilename);
output_file= fopen(outputFilename, "w");

fprintf(output_file,"\nxread\n%i %i",nucateg,nuspecs);
if (DIMS == 2 )
 fprintf(output_file,"\n&[landmark 2d]");
else
 fprintf(output_file,"\n&[landmark 3d]");

 for ( i= 0 ; i < nuspecs ; i ++)
  {
   if (i < nt)
     fprintf(output_file,"\n%s_%i ",pt_sp[ i ].sps_name,i);
   else
    fprintf(output_file,"\nnodo_%i ",i);
   for ( j= 0 ; j < nucateg ; j ++)
    {
     if (j != 0)
      fprintf(output_file,"|");
     pt_1 = consense_matrix[i][j].pt ;
     for ( l= 0 ; l < datamatrix[0].nulands ; l ++){
         if (DIMS == 3){
          fprintf(output_file,"%.6f,%.6f,%.6f ",pt_1->x,pt_1->y,pt_1->z);
          fprintf(output_file,"");}
         else{
          fprintf(output_file,"%.6f,%.6f ",pt_1->x,pt_1->y);}
        pt_1 ++ ;
        }
     }

  }

fprintf(output_file,"\n;\nproc/;");
fclose(output_file);

output_file= fopen("asis_2tnt.tmp", "w");


fprintf(output_file,"\nxread\n%i %i",nucateg,nuspecs);
if (DIMS == 2 )
 fprintf(output_file,"\n&[landmark 2d]");
else
 fprintf(output_file,"\n&[landmark 3d]");

 for ( i= 0 ; i < nuspecs ; i ++)
  {
   if (i < nt)
     fprintf(output_file,"\n%s_%i ",pt_sp[ i ].sps_name,i);
   else
    fprintf(output_file,"\nnodo_%i ",i);
   for ( j= 0 ; j < nucateg ; j ++)
    {
     if (j != 0)
      fprintf(output_file,"|");
     pt_1 = consense_matrix[i][j].pt ;
     for ( l= 0 ; l < datamatrix[0].nulands ; l ++){
         if (DIMS == 3){
          fprintf(output_file,"%.6f,%.6f,%.6f ",pt_1->x,pt_1->y,pt_1->z);
          fprintf(output_file,"");}
         else{
          fprintf(output_file,"%.6f,%.6f ",pt_1->x,pt_1->y);}
        pt_1 ++ ;
        }
     }

  }


fprintf(output_file,"\n;");


goto_printree (0) ;

 fprintf(output_file,"\nwarn-;\nsil=all;\nmacro=;\nreport-; \ncls;\ntable/7;\nclb;\ntplot];\n");
 fprintf(output_file,"var: node_fl node_tn ;\nlog trans.tmp ;\n");
 fprintf(output_file,"loop (ntax + 1) nnodes [0]\n set node_fl $$ttag #1 ; set node_tn #1 ; sil-all; if ('node_tn'!=root) quote $node_fl 'node_tn' ; else quote 'node_tn' 'node_tn' ; end;  sil=all;stop ; ");
 fprintf(output_file,"log/; log asis_2pasos.tmp ;\nlm show;\nwarn-;\nsil-all;\n lm ;\n sil=;log/;\n quit ; ");
 fprintf(output_file,"\n;\n");
 fclose(output_file);

}




int generate_alignment_shift ( int qreco,int nucas, int nuspecs, int which_cng , int timas) {
 int n,c,  cats,i;

 Sank_spcelltyp ** pt_sank ;
 Sptyp * pt_sp ;
 pt_sank = sank_mtx ;
 pt_sp = sps_list ;

 cats = define_d_pairings( qreco, nucas,  nuspecs);
 for ( n = 0 ;  n < nnods ;n ++ )
     for ( c = 0 ;  c < cats ;c ++ )
       mask_aln [n][c] = 0 ;
for ( n = 0 ;  n < nnods ;n ++ ){
     for ( c = inf_limit[n] ;  c < sup_limit[n] ;c ++ ){
       mask_aln [n][c] = 1 ;
        }
     }
for (c= 0 ; c < nnods ; c ++ )
    position [c] = inf_limit [c];


alloc_alignment (cats, nt ) ;
for (i = 0 ;  i< nt ; i ++)
  fill_alignment_w_consense_doall (i,cats,0) ;  // para shift y para asis alcanza con trabajar con inf_limit y sup_limit xq solo se corren los consensos no hay q recalcular.
                                              // para stre solo se puede hacer si los datos son continuos y hay q recalcular los limites de aln.
calculate_aln_ages  (0 ) ;
generate_aln_file (cats,which_cng) ;



   generate_tmp_file_hetero() ;
    my_spawn_hetero (   ); // largo tnt para que genere los tmps
    input_file = fopen ("trans.tmp","rb") ;
    generate_nodtrans () ;
    if ( dosvg )
      generate_d_svg(cats,0);
    fclose (input_file) ;// lee el tmp para traducir los nodos
    if (!read_tmp_data ( cats,0  )){
      printf("\nLa cagamos Carlos");

      return (0); }
remove ("chg_2tnt.tmp");
remove ( "chg_2pasos.tmp" );
remove ("trans.tmp") ;
generate_tps_shift (cats) ;

if (do_classif)
 generate_species_classif_recat (cats );

return (cats)       ;
} //generate_alignment_shift







showachange (int sp1, int sp2,int stg_asi,int stg_anc,int stg_des, int sisi  ) {
int a ,l,nodA,nodD;
Punktyp * pt_aln  ;



nodA= 99999;
nodD= 999999;

if ( sisi ){  // mapeo de asis
 sprintf(otherFilename, "pairs_%s_aln.tnt",bltype);
 output_file= fopen(otherFilename, "w");

 fprintf(output_file,"\n nstates 32;\nmxram 500;");
 fprintf(output_file,"\n '1st as is 2nd hetero'");
 fprintf(output_file,"\nxread\n%i %i",2  ,4);
  if (DIMS == 2 )
  fprintf(output_file,"\n&[landmark 2d]");
 else
  fprintf(output_file,"\n&[landmark 3d]");

 for (a= 0 ; a < 2 ; a++){
   pt_aln = optimus_matrix [nodA][stg_asi].pt ;
   if ( nodA < nt)
     fprintf(output_file,"\n%s_%i ",sps_list[ nodA ].sps_name,a);
   else
     fprintf(output_file,"\nNode_%i_%i ",nodA,a ) ;
   for ( l= 0 ; l < datamatrix[0].nulands ; l ++){
    if (DIMS == 2 )
     fprintf(output_file,"%.6f,%.6f ",pt_aln->x,pt_aln->y);
    else
     fprintf(output_file,"%.6f,%.6f,%.6f ",pt_aln->x,pt_aln->y,pt_aln->z);
    pt_aln++ ; }
     }

 for (a= 0 ; a < 2 ; a++){
   pt_aln = optimus_matrix [nodD][stg_asi].pt ;
   if ( nodD < nt)
     fprintf(output_file,"\n%s_%i ",sps_list[ nodD ].sps_name,a);
   else
     fprintf(output_file,"\nNode_%i_%i ",nodD,a ) ;
   for ( l= 0 ; l < datamatrix[0].nulands ; l ++){
    if (DIMS == 2 )
     fprintf(output_file,"%.6f,%.6f ",pt_aln->x,pt_aln->y);
    else
     fprintf(output_file,"%.6f,%.6f,%.6f ",pt_aln->x,pt_aln->y,pt_aln->z);
     pt_aln++; }}
 }
 else  // aca es con hetero
  {
  output_file= fopen(otherFilename, "a");
  if (DIMS == 2 )
   fprintf(output_file,"\n&[landmark 2d]");
  else
  fprintf(output_file,"\n&[landmark 3d]") ;
 for (a= 0 ; a < 2 ; a++){
   pt_aln = optimus_matrix [nodA][stg_anc].pt ;
   if ( nodA < nt)
     fprintf(output_file,"\n%s_%i ",sps_list[ nodA ].sps_name,a);
   else
     fprintf(output_file,"\nNode_%i_%i ",nodA,a ) ;
   for ( l= 0 ; l < datamatrix[0].nulands ; l ++){
    if (DIMS == 2 )
     fprintf(output_file,"%.6f,%.6f ",pt_aln->x,pt_aln->y);
    else
     fprintf(output_file,"%.6f,%.6f,%.6f ",pt_aln->x,pt_aln->y,pt_aln->z);
    pt_aln++ ; }
     }
 for (a= 0 ; a < 2 ; a++){
   pt_aln = optimus_matrix [nodD][stg_des].pt ;
   if ( nodD < nt)
     fprintf(output_file,"\n%s_%i ",sps_list[ nodD ].sps_name,a);
   else
     fprintf(output_file,"\nNode_%i_%i ",nodD,a ) ;
   for ( l= 0 ; l < datamatrix[0].nulands ; l ++){
    if (DIMS == 2 )
     fprintf(output_file,"%.6f,%.6f ",pt_aln->x,pt_aln->y);
    else
     fprintf(output_file,"%.6f,%.6f,%.6f ",pt_aln->x,pt_aln->y,pt_aln->z);
     pt_aln++; }
 }
  fprintf(output_file,"\n;");
  }
if (!sisi)
 fprintf(output_file,"tread (0(1(2 3))); ");
fclose(output_file) ;
}


int define_d_pairings(int qreco,int nucas, int nuspecs){
int n ,nodo, d,std_nod,std_anc,shift,stre, minlimit,maxlimit;
Sank_spcelltyp ** pt_sank ;
pt_sank = sank_mtx ;


for ( n = intnods  ;  n -- ; ){
       nodo = optlist [n] ;
       if (nodo == nt){
         inf_limit[ nodo ] = 0 ;
         sup_limit[ nodo ] = nucas   ;}
       for (d = firs[nodo] ; d != - 9  ; d = sis [ d  ] ){
          if (d < nt)
             std_nod = d ;
          else
             std_nod = recons[ qreco ][ d ] ;
          std_anc = recons[ qreco ][ nodo ] ;
          if (pt_sank[std_anc][std_nod].what_best == 0 )
             inf_limit [ d ] = inf_limit [nodo];
             sup_limit [ d ] = sup_limit [nodo];
          if (pt_sank[std_anc][std_nod].what_best == 1 ){
             shift=  pt_sank[std_anc][std_nod].best_shft ;
             shift = translator_sh [shift] ;
             inf_limit [ d ] = inf_limit [nodo] + shift ;
             sup_limit [ d ] = sup_limit [nodo] + shift ;}
          if (pt_sank[std_anc][std_nod].what_best == 2 ){
             stre=  pt_sank[std_anc][std_nod].best_str ;
             stre = translator_str [stre] ;
             inf_limit [ d ] = inf_limit [nodo] ;
             sup_limit [ d ] = sup_limit [nodo] + stre ;}

          if (pt_sank[std_anc][std_nod].what_best == 3 ){
             stre=  pt_sank[std_anc][std_nod].best_stri ;
             stre = translator_strinv [stre] ;
             inf_limit [ d ] = inf_limit [nodo] + stre ;
             sup_limit [ d ] = sup_limit [nodo] ;
             }
           if (pt_sank[std_anc][std_nod].what_best == 4 ){
             stre=  pt_sank[std_anc][std_nod].best_sh_str ;
             shift = translator_sh_str [0][stre] ;
             stre  = translator_sh_str [1][stre] ;
             inf_limit [ d ] = inf_limit [nodo] + shift ;
             sup_limit [ d ] = sup_limit [nodo] + stre ; }}}


     minlimit =9000 ; maxlimit = -3000 ;
     for ( n = 0 ;  n < nnods ;n ++ ){
        if (inf_limit [n] < minlimit)
         minlimit = inf_limit[n];
        if (sup_limit [n] > maxlimit)
         maxlimit = sup_limit[n];
         }
       maxlimit = maxlimit - minlimit ;
       for ( n = 0 ;  n < nnods ;n ++ ){
         inf_limit[n] =  inf_limit[n] - minlimit ;
         sup_limit[n] =  sup_limit[n] - minlimit ;
      
       }





 return (maxlimit );
}


void generate_alignment_pair (int nodo, int alcat) {

int ces,categs=0,l,c,i,nodp,cesp,shif_ces,shif_nod ;
Punktyp * pt_des , * pt_ces ;

nodp = nod_t2p [ nodo ] ; // el usuario pide el numero de nodo de TNT e internamente tengo que traducirlo a mi numeracion
cesp = ances   [ nodp ] ;
ces =  nod_p2t [cesp]   ;

output_file= fopen("pair_aln.tnt", "w");

for (c=0 ; c < alcat; c++ )
  if ((mask_aln [nodp][c]) && ( mask_aln [cesp][c]   ))
    categs++;

for (c=0 ; c < alcat; c++ )
  if (mask_aln [nodp][c])
    {shif_nod = c ;
    break ;}
for (c=0 ; c < alcat; c++ )
  if (mask_aln [cesp][c])
    {shif_ces = c ;
    break ;}



 fprintf(output_file,"\n xread \n %i 4 \n",categs) ;

for (c=0 ; c < alcat; c++ ) {
   if ( (!mask_aln [nodp][c]) || (!mask_aln [cesp][c])   )
    continue ;
    if (DIMS == 3 )
     fprintf(output_file,"\n&[landmark 3D]\n") ;
   else
     fprintf(output_file,"\n&[landmark 2D]\n") ;
  for (i =0 ; i < 2 ; i ++ )
  {
   pt_ces = optimus_matrix[cesp][c - shif_ces].pt ;
   if (cesp < nt)
     fprintf(output_file,"\n%s_%i ",sps_list[cesp].sps_name,i);
   else
    fprintf(output_file,"\nIntNod_%i_%i ",ces,i);
   for (l= 0 ; l < LANDS; l++){
     if (DIMS == 3 )
       fprintf(output_file,"%f,%f,%f ",pt_ces->x ,pt_ces->y,pt_ces->z) ;
     else
       fprintf(output_file,"%f,%f ",pt_ces->x ,pt_ces->y);
     pt_ces++;  }
    }
 for (i =0 ; i < 2 ; i ++ )
  {
  pt_des = optimus_matrix[nodp][c - shif_nod].pt ;
   if (nodo < nt)
     fprintf(output_file,"\n%s_%i ",sps_list[ nodp].sps_name,i);
   else
    fprintf(output_file,"\nIntNod_%i_%i ",nodo,i);
   for (l= 0 ; l < LANDS; l++){
     if (DIMS == 3 )
       fprintf(output_file,"%f,%f,%f ",pt_des->x ,pt_des->y,pt_des->z) ;
     else
       fprintf(output_file,"%f,%f ",pt_des->x ,pt_des->y);
     pt_des++;  }
    }
}
fprintf(output_file,"\n; proc/; \n") ;
fclose(output_file);
}

void generate_alignment_pair_reca (int nodo, int alcat) {

int ces,categs=0,l,c,i, nodp,cesp  ;
Punktyp * pt_des , * pt_ces;
//bandera
nodp = nod_t2p [ nodo ] ; // el usuario pide el numero de nodo de TNT e internamente tengo que traducirlo a mi numeracion
cesp = ances [ nodp ] ;
ces = nod_p2t [cesp] ;

if ( cesp == nt) // seguir aca
     cesp = firs [cesp] ;

output_file= fopen("pair_aln.tnt", "w");


for (c=0 ; c < alcat; c++ )
  if ((mask_aln [nodp][c]) && ( mask_aln [cesp][c]   ))
    categs++;

 fprintf(output_file,"\n xread \n %i 4  \n",categs) ;


 for (c=0 ; c < alcat; c++ ) {
   pt_des = optimus_matrix[nodp][c].pt ;
   pt_ces = optimus_matrix[cesp][c].pt ;
   if ( (!mask_aln [nodp][c]) || (!mask_aln [cesp][c])   )
    continue ;
    if (DIMS == 3 )
     fprintf(output_file,"\n&[landmark 3D]\n") ;
   else
     fprintf(output_file,"\n&[landmark 2D]\n") ;
  for (i =0 ; i < 2 ; i ++ )
  {
   pt_ces = optimus_matrix[cesp][c].pt ;
   if (cesp < nt)
     fprintf(output_file,"\n%s_%i ",sps_list[ cesp].sps_name,i);
   else
    fprintf(output_file,"\nIntNod_%i_%i ",ces,i);
   for (l= 0 ; l < LANDS; l++){
     if (DIMS == 3 )
       fprintf(output_file,"%f,%f,%f ",pt_ces->x ,pt_ces->y,pt_ces->z) ;
     else
       fprintf(output_file,"%f,%f ",pt_ces->x ,pt_ces->y);
     pt_ces++;  }
    }

 for (i =0 ; i < 2 ; i ++ )
  {
  pt_des = optimus_matrix[nodp][c].pt ;
   if (nodp < nt)
     fprintf(output_file,"\n%s_%i ",sps_list[ nodp].sps_name,i);
   else
    fprintf(output_file,"\nIntNod_%i_%i ",nodo,i);
   for (l= 0 ; l < LANDS; l++){
     if (DIMS == 3 )
       fprintf(output_file,"%f,%f,%f ",pt_des->x ,pt_des->y,pt_des->z) ;
     else
       fprintf(output_file,"%f,%f ",pt_des->x ,pt_des->y);
     pt_des++;  }
    }
}
fprintf(output_file,"\n; proc/; \n") ;
fclose(output_file);
}




void showme_apair ( int spa, int spb,int nucas,int reco){
int j , cual,shift,shifti, estado_ini, estado_fin;
 Sank_spcelltyp ** pt_sank ;
 Conftyp * pt_conf ;
 Sptyp * pt_sp ;
 pt_sank = sank_mtx ;
 pt_sp = sps_list ;
 pt_conf = datamatrix ;
 printf("\n---------------------------------------------");
if ((spa < nt) && (spb < nt) )
{
  printf("\nsp 0 = %s min=%f   max=%f",pt_sp[ spa ].sps_name,pt_sp[ spa ].min_age,pt_sp[ spa ].max_age  ) ;
  printf("\nsp 1 = %s min=%f   max=%f\n",pt_sp[ spb ].sps_name,pt_sp[ spb ].min_age,pt_sp[ spb ].max_age  ) ;
  printf("\nEspecie %i =%s ",spa, pt_sp[ spa ].sps_name);
  printf("\nconf |age       |which_class");
  for (j = 0 ;  j < pt_sp[spa].num_confs  ; j ++){
     cual = pt_sp[spa].conflist[j];
     printf("\n%i  | %f |   %i",cual,pt_conf[cual].age,pt_conf[cual].which_class); }

  printf("\nEspecie %i=%s",spb, pt_sp[ spb ].sps_name);
  printf("\nconf |age       |which_class");
  for (j = 0 ;  j < pt_sp[spb].num_confs  ; j ++){
     cual = pt_sp[spb].conflist[j];
     printf("\n%i  | %f |   %i",cual,pt_conf[cual].age,pt_conf[cual].which_class); }
}



estado_ini =  spa  ;
estado_fin =  spb  ;



if (doshift){
 printf ("\nshifts  ");
for (j= 0 ; j < jumany_sh ; j ++)
  printf("%i: %f|",translator_sh[j],pt_sank[estado_ini][estado_fin].score_shft [j] ) ; }
if (dostre){
printf ("\nstretchs  ");
for (j= 0 ; j < jumany_str ; j ++)
   printf("%i: %f|",translator_str[j],pt_sank[estado_ini][estado_fin].score_str [j] ) ; }
if (doinvstre){
printf ("\nstretchs_inv  ");
for (j= 0 ; j < jumany_str ; j ++)
   printf("%i: %f|",translator_str[j],pt_sank[estado_ini][estado_fin].score_str_inv [j] ) ; }


if (doshift){
printf("\nAs is= %f",pt_sank[estado_ini][estado_fin].score_asis) ;
shift=  pt_sank[estado_ini][estado_fin].best_shft ;
shifti = translator_sh [shift] ;
printf("\nBest shift (%i) %f",shifti,pt_sank[estado_ini][estado_fin].score_shft[shift]) ;}

if (dostre){
shift=  pt_sank[estado_ini][estado_fin].best_str ;
shifti = translator_str [shift] ;
printf("\nBest Stre (%i) %f",shifti,pt_sank[estado_ini][estado_fin].score_str[shift]) ;}


if (doinvstre){
shift=  pt_sank[estado_ini][estado_fin].best_stri ;
shifti = translator_str [shift] ;
printf("\nBest Stre_inv (%i) %f",shifti,pt_sank[estado_ini][estado_fin].score_str_inv[shift]) ;}


}

void put_cats_inlabels (int cats) {
   int a, i ;
   char etiqueta [200];

   for (a = 0 ; a < nnods ; a ++){
         etiqueta [0] = '\0' ;
         for (i = 0 ; i < cats  ; i ++){
          if ( (i < inf_limit [ a ]) || (i >= sup_limit [ a ]) )
            strcat(etiqueta,"-");
           else
            strcat(etiqueta,"X"); }
         strcpy (cats_labels [a],etiqueta);
   }
    for (a = 0 ; a < nnods ; a ++)
      cats_labels [a][cats]='\0';

}

void put_cats_inlabels_recat (int cats) {
   int a, i ;
   char etiqueta [200];

   for (a = 0 ; a < nnods ; a ++){
         etiqueta [0] = '\0' ;
         for (i = 0 ; i < cats  ; i ++){
          strcat(etiqueta,"X"); }
   }
    for (a = 0 ; a < nnods ; a ++)
      cats_labels [a][cats]='\0';

}


void make_as_is (sp1,sp2,nucateg,nustates) {
int    categ, cat ,a,div   ;
Punktyp * pt_sp1, * pt_sp2 ;
double dist_start,dist_end, score=0  ;

                   if (cost_ends){
                      categ =   0 ;
                      pt_sp1 = consense_matrix [sp1][ categ ].pt ; //define q celda de la sp 1 en comiezo cdo corro sp2 a la der
                      pt_sp2 = consense_matrix [ sp2 ][categ].pt ; //define q celda de la sp 2 en comiezo cdo corro sp2 a la der
                      dist_start = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                      categ = cat =   ( nucateg-1);
                      pt_sp1 = consense_matrix [sp1][categ].pt ; //define q celda de la sp 1 en final cdo corro sp2 a la izq
                      pt_sp2 = consense_matrix [sp2][categ].pt ; //define q celda de la sp 2 en final cdo corro sp2 a la izq
                      dist_end = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                      score = dist_start + dist_end ;
                      div= 2 ;
                   }else
                   {
                    for (a = 0 ; a < nucateg ; a ++){
                      pt_sp1 = consense_matrix [ sp1 ] [ a ].pt ; //define q celda de la sp 1 en comiezo cdo corro sp2 a la der
                      pt_sp2 = consense_matrix [ sp2 ] [ a ].pt ; //define q celda de la sp 2 en comiezo cdo corro sp2 a la der
                      dist_start = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
                      score += dist_start ;
                      div= nucateg; }}
                   sank_mtx[sp1][sp2].score_asis = score / div ;

}//as is


void calculate_penalty (int nuspecs,int nucateg )
 {
  int a ;

  double minscore = 3000000000, score = 0 , tot = 0 ;
for( a = 0 ; a < nuspecs  ;a ++ ){
      score = make_d_shifts_penalty(a,nucateg) ;
      tot= score  + tot ;
       if( score < minscore)
         minscore = score ;}
        tot = tot /nuspecs;
 penalty = tot / 13 ; 
 penalty = penalty  * (  pen_fac  );
 }



void conf_by_categs(nuspec,nucateg){
 int a , b , c, van, conf;
 Sptyp * pt_sp ;
 Conftyp * pt_conf ;
 pt_sp = sps_list ;
 pt_conf = datamatrix ;
  printf("   ") ;
  for (a=0 ; a < nucateg; a ++ )
      printf("%i ",a) ;
   printf("\n") ;
    for (a=0 ; a < nuspec ; a ++ ){
      printf("%i ",a) ;
      for (b=0 ; b < nucateg ; b ++ ){
         van = 0 ;
         for (c=0 ; c <  pt_sp[a].num_confs  ; c ++ ){
           conf = pt_sp[a].conflist[c];
           if (pt_conf[conf].which_class == b )
             van ++ ;}
          printf ("%i ",van);}
      printf("\n") ;}
}


double calculate_max_modif (int nucateg,int nuspecs){
int a,b,c ;
double scor, maxscore,avg_score=0 ;
Punktyp * pt_sp1, * pt_sp2 ;
for( a = 0 ; a < nuspecs  ;a ++ ){
   maxscore=-4444444 ;
   for( b = 0 ; b < nucateg  ;b ++ ){
     for ( c = 0 ; c < nucateg  ;c ++ ){
     if ( b == c )continue ;
     pt_sp1 = consense_matrix [ a ][ b ].pt ;
     pt_sp2 = consense_matrix [ a ][ c ].pt ;
     scor= pair_conf_dist (pt_sp1,pt_sp2) ;
     if (scor > maxscore)
        maxscore = scor ;
      }}
    avg_score += maxscore ;
      }
    maxscore = avg_score /nuspecs;
    return (maxscore);
}

 double  escor_fermat (Punktyp *Left, Punktyp* Right,  Punktyp* Ces, int stage,int menage)
{
   double dis_Izq, dis_Der, dis_Anc, fermat ;
   int c,nupoints ;
   Punktyp medio ;
   fermat= 0 ;
   nupoints = LANDS ;

   for (c= 0; c< nupoints ; c++) {

        if (DIMS == 2 ) {
         dofermatpoint_2d (*Left,*Right,*Ces,&medio) ; //ahi deberia modificarse el punto medio veremos....
         dis_Izq=   sqrt (  (  pow ((Left->x -  medio.x),2)  + pow ( (Left->y  - medio.y),2 )  ) ) ;
         dis_Der=   sqrt (  (  pow ((Right->x - medio.x),2)  + pow ( (Right->y - medio.y),2 )  ) ) ;
         dis_Anc=   sqrt (  (  pow ((Ces->x -   medio.x),2)  + pow ( (Ces->y   - medio.y),2 )  ) ) ;
        }
        else
        {
         dofermatpoint_3d (*Left,*Right,*Ces,&medio) ; //ahi deberia modificarse el punto medio veremos...
         dis_Izq=   sqrt (  (  pow ((Left->x -  medio.x),2)  + pow ( (Left->y  - medio.y),2 ) + pow ( (Left->z  - medio.z),2 ) ) ) ;
         dis_Der=   sqrt (  (  pow ((Right->x - medio.x),2)  + pow ( (Right->y - medio.y),2 ) + pow ( (Right->z - medio.z),2 ) ) ) ;
         dis_Anc=   sqrt (  (  pow ((Ces->x -   medio.x),2)  + pow ( (Ces->y   - medio.y),2 ) + pow ( (Ces->z   - medio.z),2 ) ) ) ;
        }
        if ( menage == 9 ) { // esto es para armar los estados de fx extendido
          consense_matrix [ dde_cns_mtx ][stage].pt[c].x = medio.x ;
          consense_matrix [ dde_cns_mtx ][stage].pt[c].y = medio.y ;
          if (DIMS == 3 )
           consense_matrix [ dde_cns_mtx ][stage].pt[c].z = medio.z ;}
     
        fermat = fermat + dis_Izq + dis_Der + dis_Anc ;
        Left++; Right++ ; Ces++ ; }

return (fermat) ;
}
void dofermatpoint_2d ( Punktyp Izq , Punktyp Der , Punktyp Anc , Punktyp * middle )
{
 double X_Izq, Y_Izq, X_Der, Y_Der, X_Anc, Y_Anc, X_Nod, Y_Nod ;
 double angulo_Izq, angulo_Der, angulo_Anc, suma, Lado_ID, Lado_IA, Lado_DA ;
 int izquierdo, derecho, ancestro;
 double X_1, X_2, X_3, Y_1, Y_2, Y_3 ;
 double vert_X_Eq, vert_Y_Eq, Lado_12, Lado_13, ang_sis ;
 double Pen_12, Ord_12, Pen_13, Ord_13,  Pendiente_ID, Pendiente_IA, Pendiente_DA ;
 int listo ;

 listo = 0 ;


 X_1 = ( Izq.x - Der.x ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 10e-13 ) Izq.x = Der.x ;
 X_1 = ( Izq.y - Der.y ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 10e-13 ) Izq.y = Der.y ;
 X_1 = ( Izq.x - Anc.x ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 10e-13 ) Izq.x = Anc.x ;
 X_1 = ( Izq.y - Anc.y ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 10e-13 ) Izq.y = Anc.y ;
 X_1 = ( Der.x - Anc.x ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 10e-13 ) Der.x = Anc.x ;
 X_1 = ( Der.y - Anc.y ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 10e-13 ) Der.y = Anc.y ;


if ( Anc.x < ANY_POINT ) { // This must be the first node up
   if ( Izq.x < ANY_POINT ) {
       middle -> x = Der.x ;
       middle -> y = Der.y ;
       return ; }
   if ( Der.x < ANY_POINT ) {
       middle -> x = Izq.x ;
       middle -> y = Izq.y ;
       return ; }
   middle -> x = ( Izq.x + Der.x ) / 2 ;
   middle -> y = ( Izq.y + Der.y ) / 2 ;
   return ; }

if ( Izq.x < ANY_POINT || Der.x < ANY_POINT ) {
    if ( Izq.x < ANY_POINT && Der.x < ANY_POINT ) {
        middle -> x = Anc.x ;
        middle -> y = Anc.y ; }
    else {
       if ( Izq.x < ANY_POINT ) {
           middle -> x = ( Anc.x + Der.x ) / 2 ;
           middle -> y = ( Anc.y + Der.y ) / 2 ; }
       else {
           middle -> x = ( Anc.x + Izq.x ) / 2 ;
           middle -> y = ( Anc.y + Izq.y ) / 2 ; }}
    return ; }

 X_Izq = Izq.x ;  Y_Izq = Izq.y ;
 X_Der = Der.x ;  Y_Der = Der.y ;
 X_Anc = Anc.x ;  Y_Anc = Anc.y ;
 Lado_ID = Distanciero_2d ( X_Der, Y_Der, X_Izq, Y_Izq) ;
 Lado_IA = Distanciero_2d ( X_Anc, Y_Anc, X_Izq, Y_Izq) ;
 Lado_DA = Distanciero_2d ( X_Anc, Y_Anc, X_Der, Y_Der) ;

//PASO 1.0: Hay dos puntos con la mismas coordenadas?
if ((Y_Izq==Y_Der) && (X_Izq==X_Der))
   { X_Nod=X_Izq ; Y_Nod=Y_Izq ;//printf ("\n Pto Fermat es el punto Der=Izq\n") ;
   listo = listo +1 ; }

if ((Y_Izq==Y_Anc) && (X_Izq==X_Anc))
   { X_Nod=X_Izq ; Y_Nod=Y_Izq ; //printf ("\n Pto Fermat es el punto Anc=Izq\n") ;
    listo = listo +1 ; }

if ((Y_Der==Y_Anc) && (X_Der==X_Anc))
    { X_Nod=X_Der ; Y_Nod=Y_Der; //printf ("\n Pto Fermat es el punto Anc=Der\n") ;
   listo = listo +1 ; }

//PASO 1.1: Hay un angulo de 120 o mas grados? Esto lo resuelvo usando el teorema del coseno
//  cos A =  ( b^2 + c^2-a^2 ) / 2bc
 suma = ( (Lado_ID *  Lado_ID)  + (Lado_IA * Lado_IA) - (Lado_DA * Lado_DA) ) / (2*Lado_IA*Lado_ID) ;
 if ( suma > 1 ) suma = 1 ;
 if ( suma < -1 ) suma = 1 ;
 angulo_Izq = acos ( suma ) ;
 angulo_Izq = (angulo_Izq *180)/3.14159     ;
 suma = ( (Lado_ID * Lado_ID)  + (Lado_DA * Lado_DA) - (Lado_IA * Lado_IA) ) / (2*Lado_ID*Lado_DA) ;
 if ( suma > 1 ) suma = 1 ;
 if ( suma < -1 ) suma = 1 ;
 angulo_Der = acos ( suma ) ;
 angulo_Der = (angulo_Der *180)/3.14159     ;
 suma = ( (Lado_IA * Lado_IA)  + (Lado_DA * Lado_DA) - (Lado_ID * Lado_ID) ) / (2*Lado_DA*Lado_IA) ;
 if ( suma > 1 ) suma = 1 ;
 if ( suma < -1 ) suma = 1 ;
 angulo_Anc = acos ( suma ) ;
 angulo_Anc = (angulo_Anc *180)/3.14159     ;

 if ( listo < 1 ) {
  if (  ( ( angulo_Izq + angulo_Der ) < 60 ) ||
        ( ( angulo_Izq + angulo_Anc ) < 60 ) ||
        ( ( angulo_Der + angulo_Anc ) < 60 ) ) {
     if ( Lado_IA > Lado_ID ) {
         if ( Lado_IA > Lado_DA ) {
             X_Nod = X_Der ; Y_Nod = Y_Der ; }
         else {
             X_Nod = X_Izq ; Y_Nod = Y_Izq ; }}
     else if ( Lado_ID > Lado_DA ) {
               X_Nod = X_Anc ; Y_Nod = Y_Anc ; }
           else {
               X_Nod = X_Izq ; Y_Nod = Y_Izq ; }
     listo = 1 ; }}

Pendiente_ID =  ((Y_Izq - Y_Der) / (X_Izq - X_Der)) ;
Pendiente_IA =  ((Y_Izq - Y_Anc) / (X_Izq - X_Anc)) ;
Pendiente_DA =  ((Y_Der - Y_Anc) / (X_Der - X_Anc)) ;

//PASO 1.2. Me fijo que nodo es el que esta mas a la izquierda y a ese sera el 1. El 2 sera aquel en que termine el lados superior y
//el tres ser?aquel en que termine el lado inferior.

if (listo<1)
{
 if ((X_Izq == X_Der ) && (X_Izq < X_Anc ) )
    { if (Y_Izq > Y_Der)
          { izquierdo = 1 ; derecho = 3 ; ancestro = 2 ;
            Lado_13 = Lado_ID ; Lado_12 = Lado_IA ;
            X_1= X_Izq; Y_1 =Y_Izq ; X_3 = X_Der ;  Y_3 = Y_Der ; X_2 = X_Anc ;  Y_2 = Y_Anc ; }
      else
          { izquierdo = 3 ; derecho = 1 ; ancestro = 2 ;
            Lado_13 = Lado_ID ; Lado_12 = Lado_DA ;
            X_1= X_Der; Y_1= Y_Der; X_2 = X_Anc ;  Y_2 = Y_Anc ; X_3 = X_Izq ;  Y_3 = Y_Izq ; }}
 else
    {
      if ((X_Izq == X_Anc ) && (X_Izq < X_Der ) )
        {
          if (Y_Izq > Y_Anc)
           {
             izquierdo = 1 ; derecho = 2 ; ancestro = 3 ;
             Lado_13 = Lado_IA ; Lado_12 = Lado_ID ;
             X_1= X_Izq; Y_1 =Y_Izq ; X_2 = X_Der ;  Y_2 = Y_Der ; X_3 = X_Anc ;  Y_3 = Y_Anc ;
           }
           else
           {
             izquierdo = 3 ; derecho = 2 ; ancestro = 1 ; Lado_13 = Lado_IA ; Lado_12 = Lado_DA ;
             X_1= X_Anc; Y_1 =Y_Anc ; X_2 = X_Der ;  Y_2 = Y_Der ; X_3 = X_Izq ;  Y_3 = Y_Izq ;
           }
        }
      else
        if ((X_Der == X_Anc ) && (X_Der < X_Izq ) )
         {
           if (Y_Der > Y_Anc)
            {
             izquierdo = 2 ; derecho = 1 ; ancestro = 3 ; Lado_13 = Lado_DA ; Lado_12 = Lado_ID ;
             X_2= X_Izq; Y_2 =Y_Izq ; X_1 = X_Der ;  Y_1 = Y_Der ; X_3 = X_Anc ;  Y_3 = Y_Anc ;
            }
           else
            {
              izquierdo = 2 ; derecho = 3 ; ancestro = 1 ;
              Lado_13 = Lado_DA ; Lado_12 = Lado_IA ;
              X_1= X_Anc; Y_1 =Y_Anc ; X_2 = X_Izq ;  Y_2 = Y_Izq ; X_3 = X_Der ;  Y_3 = Y_Der ;
            }
         }
     }

  if ((X_Izq < X_Der) && (X_Izq < X_Anc) )
   {
      izquierdo = 1 ;
      X_1 = X_Izq ; Y_1 = Y_Izq ;
      if ( Pendiente_ID  > Pendiente_IA )
     {
       derecho = 2 ;
       ancestro = 3 ;
       Lado_13 = Lado_IA ;
       Lado_12 = Lado_ID ;
       X_2 = X_Der ;  Y_2 = Y_Der ; X_3 = X_Anc ;  Y_3 = Y_Anc ;
     }
     else
     {
       derecho = 3 ;
       ancestro = 2 ;
       Lado_12 = Lado_IA ;
       Lado_13 = Lado_ID ;
       X_3 = X_Der ;  Y_3 = Y_Der ; X_2 = X_Anc ;  Y_2 = Y_Anc ;
      }
  }
  if ((X_Anc < X_Izq) && (X_Anc < X_Der) )
   {
    ancestro = 1 ;
    X_1 = X_Anc ; Y_1 = Y_Anc ;
    if (Pendiente_DA > Pendiente_IA)
       {
        derecho = 2 ;
        izquierdo = 3 ;
        Lado_12 = Lado_DA ;
        Lado_13 = Lado_IA ;
        X_2 = X_Der ;  Y_2 = Y_Der ; X_3 = X_Izq ;  Y_3 = Y_Izq ;
       }
     else
       {
        derecho = 3 ;
        izquierdo = 2 ;
        Lado_13 = Lado_DA ;
        Lado_12 = Lado_IA ;
        X_3 = X_Der ;  Y_3 = Y_Der ; X_2 = X_Izq ;  Y_2 = Y_Izq ;
       }
   }

   if ((X_Der < X_Anc) && (X_Der < X_Izq) )
   {
      derecho = 1 ;
      X_1 = X_Der ; Y_1 = Y_Der ;

         if (Pendiente_DA >= Pendiente_ID )
         {
           ancestro = 2 ;
           izquierdo = 3 ;
           Lado_12 = Lado_DA ;
           Lado_13 = Lado_ID ;
           X_2 = X_Anc ;  Y_2 = Y_Anc ; X_3 = X_Izq ;  Y_3 = Y_Izq ;
         }
         else
         {
          ancestro = 3 ;
          izquierdo = 2 ;
          Lado_13 = Lado_DA ;
          Lado_12 = Lado_ID ;
          X_3 = X_Anc ;  Y_3 = Y_Anc ; X_2 = X_Izq ;  Y_2 = Y_Izq ;
         }

    }

//PASO 2.1.1: Calculo el Vertice del triangulo equilatero correspondiente al lado 1-2.

ang_sis = atan ( (Y_2 - Y_1 ) / (X_2 - X_1 ) ) ;//calculo del angulo entre el lado y el sist de referencia
vert_X_Eq = X_1 + (cos (ang_sis) * 0.5 * Lado_12 ) - cos (( PI * 0.5) - ang_sis) * Lado_12 * cos (0.5235987756) ;
vert_Y_Eq = Y_1 + (sin (ang_sis) * 0.5 * Lado_12 ) + sin (( PI * 0.5)  - ang_sis) * Lado_12 * cos (0.5235987756) ;



//PASO 2.1.2: Calculo de la funcion de la recta
 Pen_12 = ((Y_3 - vert_Y_Eq ) / (X_3 - vert_X_Eq) ) ;
 Ord_12 = (  vert_Y_Eq - (Pen_12 * vert_X_Eq)   ) ;

//PASO 2.2.1: Calculo el Vertice del triangulo correspondiente al lado 1-3.
ang_sis = atan ( (Y_3 - Y_1 ) / (X_3 - X_1 ) ) ;
vert_X_Eq = X_1 + (cos (ang_sis) * 0.5 * Lado_13 ) + cos (( PI * 0.5) - ang_sis) * Lado_13 * cos (0.5235987756) ;
vert_Y_Eq = Y_1 + (sin (ang_sis) * 0.5 * Lado_13 ) - sin (( PI * 0.5) - ang_sis) * Lado_13 * cos (0.5235987756) ;

//PASO 2.2.2: Calculo de la funcion de la otra recta
 Pen_13 = ((Y_2 - vert_Y_Eq ) / (X_2 - vert_X_Eq) ) ;
 Ord_13 = (  vert_Y_Eq - (Pen_13 * vert_X_Eq)   ) ;

//PASO 3.1.: SOLUCION DEL SISTEMA DE DOS ECUACIONES
  X_Nod = ( Ord_12 - Ord_13 ) / (Pen_13 - Pen_12 ) ;
  Y_Nod = X_Nod *  Pen_12 + Ord_12 ;

}

middle -> x = X_Nod ;
middle -> y = Y_Nod ;

}

double Distanciero_2d (double X2, double Y2, double X1, double Y1)
{

   double lado_X ;
   double lado_Y ;
   double squareY  ;
   double squareX  ;
   double suma ;
   double raiz ;

    lado_X = X2 - X1 ;
    lado_Y = Y2 - Y1 ;
    squareX = lado_X * lado_X ;
    squareY = lado_Y * lado_Y ;
    suma= squareX + squareY ;
    raiz = sqrt ( suma ) ;
    return (raiz) ;
}// end Distanciero_2d


void dofermatpoint_3d ( Punktyp Izq , Punktyp Der , Punktyp Anc , Punktyp * middle )
{

int  j , k ;
double Cte_prop ;
double X_Der ;
double Y_Der ;
double Z_Der ;
double X_Izq ;
double Y_Izq ;
double Z_Izq ;
double X_Anc ;
double Y_Anc ;
double Z_Anc ;
double X_Nod ;
double Y_Nod ;
double Z_Nod ;
double X_No ;
double Y_No ;
double Lado_ID ;
double Lado_DA ;
double Lado_IA ;
double X_1, Y_1, X_2 , Y_2, X_3, Y_3 ;
double X_23, Y_23, Dist23F, DistF, DistI23, DistK, X, Y, Z ;
double angulo_Anc ;
double angulo_Izq ;
double angulo_Der ;
double angulo_AncG ;
double angulo_IzqG ;
double angulo_DerG ;
int listo = 0 , rotado = 0 ;
double vert_X_Eq ;
double vert_Y_Eq ;
double Lado_12 ;
double Lado_13 ;
double ang_sis ;
double Pen_12 ;
double Ord_12 ;
double Pen_13 ;
double Ord_13 ;
double tmp ;

if ( Anc.x < ANY_POINT ) { // This must be the first node up
   if ( Izq.x < ANY_POINT ) {
       middle -> x = Der.x ;
       middle -> y = Der.y ;
       middle -> z = Der.z ;
       return ; }
   if ( Der.x < ANY_POINT ) {
       middle -> x = Izq.x ;
       middle -> y = Izq.y ;
       middle -> z = Der.z ;
       return ; }
   middle -> x = ( Izq.x + Der.x ) / 2 ;
   middle -> y = ( Izq.y + Der.y ) / 2 ;
   middle -> z = ( Izq.z + Der.z ) / 2 ; }


 X_1 = ( Izq.x - Der.x ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 0.0000000001 ) Izq.x = Der.x ;
 X_1 = ( Izq.y - Der.y ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 0.0000000001 ) Izq.y = Der.y ;
 X_1 = ( Izq.x - Anc.x ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 0.0000000001 ) Izq.x = Anc.x ;
 X_1 = ( Izq.y - Anc.y ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 0.0000000001 ) Izq.y = Anc.y ;
 X_1 = ( Der.x - Anc.x ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 0.0000000001 ) Der.x = Anc.x ;
 X_1 = ( Der.y - Anc.y ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 0.0000000001 ) Der.y = Anc.y ;
 X_1 = ( Izq.z - Der.z ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 0.0000000001 ) Izq.z = Der.z ;
 X_1 = ( Anc.z - Der.z ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 0.0000000001 ) Anc.z = Der.z ;
 X_1 = ( Izq.z - Anc.z ) / fermat_scale ; if ( X_1 < 0 ) X_1 = -X_1 ; if ( X_1 < 0.0000000001 ) Izq.z = Anc.z ;


 X_Der = Der.x;
 Y_Der = Der.y;
 Z_Der = Der.z;
 X_Izq = Izq.x;
 Y_Izq = Izq.y;
 Z_Izq = Izq.z;
 X_Anc = Anc.x ;
 Y_Anc = Anc.y ;
 Z_Anc = Anc.z ;

if ( Izq.x < ANY_POINT || Der.x < ANY_POINT ) {
    if ( Izq.x < ANY_POINT && Der.x < ANY_POINT ) {
        middle -> x = Anc.x ;
        middle -> y = Anc.y ;
        middle -> z = Anc.z ; }
    else {
       if ( Izq.x < ANY_POINT ) {
           middle -> x = ( Anc.x + Der.x ) / 2 ;
           middle -> y = ( Anc.y + Der.y ) / 2 ;
           middle -> z = ( Anc.z + Der.z ) / 2 ; }
       else {
           middle -> x = ( Anc.x + Izq.x ) / 2 ;
           middle -> y = ( Anc.y + Izq.y ) / 2 ;
           middle -> z = ( Anc.z + Izq.z ) / 2 ; }}
    return ; }

Lado_ID = Distanciero_3d ( X_Der, Y_Der ,Z_Der, X_Izq, Y_Izq, Z_Izq) ;
Lado_IA = Distanciero_3d ( X_Anc, Y_Anc, Z_Anc, X_Izq, Y_Izq, Z_Izq) ;
Lado_DA = Distanciero_3d ( X_Anc, Y_Anc, Z_Anc, X_Der, Y_Der, Z_Der) ;


//PASO 1.0: Hay dos puntos con la mismas coordenadas?
if ((Y_Izq==Y_Der) && (X_Izq==X_Der) && (Z_Izq==Z_Der) )
   { X_Nod=X_Izq ; Y_Nod=Y_Izq ; Z_Nod = Z_Izq ;
   listo = 1 ; }

if ((Y_Izq==Y_Anc) && (X_Izq==X_Anc) && (Z_Izq==Z_Anc) )
   { X_Nod=X_Izq ; Y_Nod=Y_Izq ; Z_Nod = Z_Anc ;
     listo = 1 ; }

if ((Y_Der==Y_Anc) && (X_Der==X_Anc) && (Z_Der==Z_Anc) )
    { X_Nod=X_Der ; Y_Nod=Y_Der; Z_Nod = Z_Der ;
      listo = 1 ; }

//PASO 1.1: Hay un angulo de 120 o mas grados? Esto lo resuelvo usando el teorema del coseno
//  cos A =  ( b^2 + c^2-a^2 ) / 2bc
if ( listo < 1 ) {
 tmp = ( (Lado_ID *  Lado_ID)  + (Lado_IA * Lado_IA) - (Lado_DA * Lado_DA) ) / (2*Lado_IA*Lado_ID) ;
 if ( tmp > 1 ) tmp = 1 ;
 if ( tmp < -1 ) tmp = -1 ;
 angulo_Izq = acos ( tmp ) ;
 angulo_IzqG = (angulo_Izq *180)/PI     ;
 tmp = ( (Lado_ID * Lado_ID)  + (Lado_DA * Lado_DA) - (Lado_IA * Lado_IA) ) / (2*Lado_ID*Lado_DA) ;
 if ( tmp > 1 ) tmp = 1 ;
 if ( tmp < -1 ) tmp = -1 ;
 angulo_Der = acos ( tmp ) ;
 angulo_DerG = (angulo_Der *180)/PI ;
 tmp = ( (Lado_IA * Lado_IA)  + (Lado_DA * Lado_DA) - (Lado_ID * Lado_ID) ) / (2*Lado_DA*Lado_IA) ;
 if ( tmp > 1 ) tmp = 1 ;
 if ( tmp < -1 ) tmp = -1 ;
 angulo_Anc = acos ( tmp ) ;
 angulo_AncG = (angulo_Anc *180)/PI     ;
 if (  ( ( angulo_IzqG + angulo_DerG ) < 60 ) ||
        ( ( angulo_IzqG + angulo_AncG ) < 60 ) ||
        ( ( angulo_DerG + angulo_AncG ) < 60 ) ) {
     if ( Lado_IA > Lado_ID ) {
         if ( Lado_IA > Lado_DA )
            { X_Nod = X_Der ; Y_Nod = Y_Der ; Z_Nod = Z_Der ;}
         else {
             X_Nod = X_Izq ; Y_Nod = Y_Izq ; Z_Nod = Z_Izq ;}}
     else if ( Lado_ID > Lado_DA ) {
               X_Nod = X_Anc ; Y_Nod = Y_Anc ; Z_Nod = Z_Anc ; }
           else {
               X_Nod = X_Izq ; Y_Nod = Y_Izq ; Z_Nod = Z_Izq ; }
     listo = 1 ; }}

if (listo < 1)
{

  if (angulo_IzqG < 90)
    {
    X_1= 0;
    Y_1 =0 ;
    X_2 = Lado_ID * cos (angulo_Izq) ;
    Y_2 = Lado_ID * sin (angulo_Izq) ;
    X_3 = Lado_IA ;
    Y_3 = 0 ;
    Lado_12 = Lado_ID ;
    Lado_13 = Lado_IA ;
   // printf ("entro en angulo menor que 90\n") ;
    }
 else
    {
   //  printf ("entro en angulo mayor que 90\n") ;
    X_1= 0;
    Y_1 =0 ;
    X_2 = Lado_DA * cos (angulo_Der) ;
    Y_2 = Lado_DA * sin (angulo_Der) ;
    X_3 = Lado_ID ;
    Y_3 = 0 ;
    Lado_12 = Lado_DA ;
    Lado_13 = Lado_ID ;
    Lado_12 = Lado_DA ;
    Lado_13 = Lado_ID ;
    rotado = 1 ;
    }
//calculo del angulo entre el lado y el sist de referencia
 ang_sis = atan ( (Y_2 - Y_1 ) / (X_2 - X_1 ) ) ;


 vert_X_Eq = X_1 + (cos (ang_sis) * 0.5 * Lado_12 ) - cos ((PI * 0.5) - ang_sis) * Lado_12 * cos (0.5235987756) ;
 vert_Y_Eq = Y_1 + (sin (ang_sis) * 0.5 * Lado_12 ) + sin ((PI * 0.5)  - ang_sis) * Lado_12 * cos (0.5235987756) ;



//PASO 2.1.2: Calculo de la funcion de la recta
 Pen_12 = ((Y_3 - vert_Y_Eq ) / (X_3 - vert_X_Eq) ) ;
 Ord_12 = (  vert_Y_Eq - (Pen_12 * vert_X_Eq)   ) ;

//PASO 2.2.1: Calculo el Vertice del triangulo correspondiente al lado 1-3.
ang_sis = atan ( (Y_3 - Y_1 ) / (X_3 - X_1 ) ) ;
vert_X_Eq = X_1 + (cos (ang_sis) * 0.5 * Lado_13 ) + cos ((PI * 0.5) - ang_sis) * Lado_13 * cos (0.5235987756) ;
vert_Y_Eq = Y_1 + (sin (ang_sis) * 0.5 * Lado_13 ) - sin ((PI * 0.5) - ang_sis) * Lado_13 * cos (0.5235987756) ;

//PASO 2.2.2: Calculo de la funcion de la otra recta
 Pen_13 = ((Y_2 - vert_Y_Eq ) / (X_2 - vert_X_Eq) ) ;
 Ord_13 = (  vert_Y_Eq - (Pen_13 * vert_X_Eq)   ) ;

//PASO 3.1.: SOLUCION DEL SISTEMA DE DOS ECUACIONES

  X_No = ( Ord_12 - Ord_13 ) / (Pen_13 - Pen_12 ) ;
  Y_No = X_No *  Pen_12 + Ord_12 ;

//printf ("XNo cuesta:%f \n", X_No) ;
//printf ("YNo cuesta:%f \n", Y_No) ;
//printf ("pen13:%f \n", Pen_13) ;


//voy a calcular la distancia entre Des y el punto donde corta el lado AD la recta del pto de fermat
 Pen_12 = (Y_No / X_No)  ; //printf ("pen12:%f \n", Pen_12) ;
 Ord_12 = 0 ;


Cte_prop =  (X_3 - X_2 )  ;
    //printf ("\Cte_prop %f \n", Cte_prop) ;

 if ( ( (X_3 - X_2 )  < 0.000000001) && ( (X_3 - X_2 )  > - 0.000000001) )
  {
      Dist23F = Y_2 - Y_No ;
      X_23 = X_3 ;
      Y_23 = Pen_12 *  X_23 ;
     // printf ("\entro Dist23F %f Y_23 %f X_23 %f \n",Dist23F, Y_23 , X_23  ) ;
  }
 else
  {
 Pen_13 = (Y_3 - Y_2 ) / (X_3 - X_2) ;  //printf ("\n pen13:%f \n", Pen_13) ;
 Ord_13 = Y_2 - (Pen_13 * X_2) ;    //  printf ("\n ord:%f \n", Ord_13) ;
 X_23 = ( Ord_12 - Ord_13 ) / (Pen_13 - Pen_12 ) ; //printf ("\n X_23 :%f \n", X_23 ) ;
 Y_23 =  X_23 *  Pen_12 + Ord_12 ;               ; //printf ("\n Y_23 :%f \n", Y_23 ) ;
 Dist23F= Distanciero_3d (X_2, Y_2 ,0 , X_23, Y_23, 0 ) ;  //printf ("\n  Dist23F :%f \n",  Dist23F ) ;
  }


//voy a calcular la distancia entre Ñ y Fermat sobre la recta anterior.

DistF= Distanciero_3d (X_No, Y_No ,0 ,0 , 0, 0 ) ; //printf ("\n  DistF :%f \n",  DistF ) ;

//voy a calcular la distancia entre Izq y Ñ

DistI23= Distanciero_3d (X_23, Y_23 ,0 ,0 , 0, 0 ) ; //printf ("\n  DistI23 :%f \n",  DistI23 ) ;
//printf ("\n Lado_DA :%f \n",  Lado_DA ) ;
DistK= DistI23 - DistF ;

if (rotado == 0 )
{
Cte_prop =   1 - (( Lado_DA - Dist23F ) / Lado_DA) ;


if (X_Der > X_Anc)
 X = X_Der - (X_Der - X_Anc) * Cte_prop ;
else
 X = X_Der + (X_Anc - X_Der ) * Cte_prop ;
if (Y_Der > Y_Anc)
 Y = Y_Der -  (Y_Der - Y_Anc) * Cte_prop;
else
 Y = Y_Der + ( Y_Anc - Y_Der ) * Cte_prop ;
if (Z_Der > Z_Anc)
 Z = Z_Der - ( Z_Der - Z_Anc ) * Cte_prop ;
else
 Z = Z_Der + (Z_Anc - Z_Der  ) * Cte_prop ;

Cte_prop =  1- ((DistI23 - DistF) / DistI23 );

if (X_Izq > X )  // las distancias estan mediddas desde Izq
 X_Nod = X_Izq - (X_Izq - X) * Cte_prop ;
else
 X_Nod = X_Izq + (X - X_Izq  ) * Cte_prop ;
if (Y_Izq > Y  )
 Y_Nod = Y_Izq - ( Y_Izq - Y ) * Cte_prop ;
else
 Y_Nod = Y_Izq + (Y - Y_Izq ) * Cte_prop ;

if ( Z_Izq > Z)
 Z_Nod = Z_Izq - (Z_Izq - Z) * Cte_prop ;
else
 Z_Nod = Z_Izq + (Z - Z_Izq ) * Cte_prop ;
} //if (rotado)

  else
   {

Cte_prop =   1 - (( Lado_IA - Dist23F ) / Lado_IA) ;
//printf ("\n\n cte prop :%f \n", Cte_prop) ;
if (X_Anc > X_Izq)
 X = X_Anc - (X_Anc - X_Izq) * Cte_prop ;
else
 X = X_Anc + ((X_Izq - X_Anc ) * Cte_prop) ;
 //printf ("\naca X_Anc %f, X_Izq %f, Cte\n %f", X_Anc, X_Izq, Cte_prop ) ;
if (Y_Anc > Y_Izq)
 Y = Y_Anc -  (Y_Anc - Y_Izq) * Cte_prop;
else
 Y = Y_Anc + ( Y_Izq - Y_Anc ) * Cte_prop ;
if (Z_Anc > Z_Izq)
 Z = Z_Anc - ( Z_Anc - Z_Izq ) * Cte_prop ;
else
 Z = Z_Anc + (Z_Izq - Z_Anc  ) * Cte_prop ;


Cte_prop =  1- ((DistI23 - DistF) / DistI23 );


if (X_Der > X )  // las distancias estan mediddas desde Der
 X_Nod = X_Der - (X_Der - X) * Cte_prop ;
else
 X_Nod = X_Der + (X - X_Der  ) * Cte_prop ;
//printf ("\naca X_Der %f, X %f, X_Nod %f", X_Der, X, X_Nod) ;
if (Y_Der > Y  )
 Y_Nod = Y_Der - ( Y_Der - Y ) * Cte_prop ;
else
 Y_Nod = Y_Der + (Y - Y_Der ) * Cte_prop ;

if ( Z_Der > Z)
 Z_Nod = Z_Der - (Z_Der - Z) * Cte_prop ;
else
 Z_Nod = Z_Der + (Z - Z_Der ) * Cte_prop ;
} // else de if rotado


} // if (listo < 1)

if ( X_Nod > 10000000 || X_Nod < -10000000 || Y_Nod > 10000000 || Y_Nod < -10000000 || Z_Nod > 10000000 || Z_Nod < -10000000 ) {
  X_Nod = middle -> x ;
  Y_Nod = middle -> y ;
  Z_Nod = middle -> z ;
  DistK = CURSUM ;
  X_3 = DistK ;
  middle -> x = ( Der.x + Izq.x + Anc.x ) / 3 ;
  middle -> y = ( Der.y + Izq.y + Anc.y ) / 3 ;
  middle -> z = ( Der.z + Izq.z + Anc.z ) / 3 ;
  j = 0 ;
  while ( 1 ) {
    Cte_prop = 0.0000001 ;
    X_2 = X_3 ;  // X_2 = CURSUM ;
    SLIDE_POINT( middle -> x , Der.x , Izq.x , Anc.x ) ;
    SLIDE_POINT( middle -> y , Der.y , Izq.y , Anc.y ) ;
    SLIDE_POINT( middle -> z , Der.z , Izq.z , Anc.z ) ;
    ++ j ;
    X_3 = CURSUM ;
    if ( X_3 - X_2 < 0.0000001 ) break ; }
  if ( DistK < X_3 ) {
    middle -> x = X_Nod ;
    middle -> y = Y_Nod ;
    middle -> z = Z_Nod ; }
  return ; }

middle -> x = X_Nod ;
middle -> y = Y_Nod ;
middle -> z = Z_Nod ;

} //dofermatpoint3d

double Distanciero_3d (double X2, double Y2, double Z2, double X1, double Y1,double Z1)
{
   double lado_Z ;
   double lado_X ;
   double lado_Y ;
   double squareY  ;
   double squareX  ;
   double squareZ  ;
   double suma ;
   double raiz ;

    lado_X = X2 - X1 ;
    lado_Y = Y2 - Y1 ;
    lado_Z = Z2 - Z1 ;
    squareX = lado_X * lado_X ;
    squareY = lado_Y * lado_Y ;
    squareZ = lado_Z * lado_Z ;
    suma= squareX + squareY + squareZ ;
    raiz = sqrt (suma) ;
    return (raiz) ;
}// end Distanciero


void make_d_shifts_menage_trois (int  nucateg,int sp1,int sp2,int sp3){
int  i,j,move  , guich,stg_star_m, stg_fin_m, besti ;
Punktyp * pt_sp1, * pt_sp2, * pt_sp3 ;

double bescore=1000000000, score  ;
move =  0 ;

 for (i = - ( nucateg - 2 ) ; i < ( nucateg - 1)  ; i ++ )
 {
      if (i==0 ) continue ;
   if ( i < 0 )
    {
      stg_star_m = -i ;stg_fin_m = nucateg + i  ;
      for (j = 0 ; j <  nucateg; j++)
      {
        if (j < stg_fin_m)
          {
           guich = stg_star_m + j ;
           pt_sp1 = consense_matrix [sp1][j].pt ;
           pt_sp2 = consense_matrix [sp2][j].pt ;
           pt_sp3 = consense_matrix [sp3][guich].pt ;
        //   printf("\narriba i=%i , j=%i , guich=%i",i,j,guich);
           score= escor_fermat (pt_sp1,pt_sp2,pt_sp3,j,9);
          }
        else
        {
             pt_sp1 = consense_matrix [sp1][j].pt ;
             cpy_one (sp1,j) ;
            }
      }
    }
    else
     {
      stg_star_m = i ;  guich= 0 ;
      for (j = 0 ; j <  nucateg; j++)
      {
       if (j < stg_star_m)
        {
             pt_sp1 = consense_matrix [sp1][j].pt ;
             cpy_one (sp1,j) ;
            }
         else
          {
           pt_sp1 = consense_matrix [sp1][j].pt ;
           pt_sp2 = consense_matrix [sp2][j].pt ;
           pt_sp3 = consense_matrix [sp3][guich].pt ;
          // printf("\nabajo i=%i , j=%i , guich=%i",i,j,guich);
           guich++ ;
           score= escor_fermat (pt_sp1,pt_sp2,pt_sp3,j,9);
           }
      }
    }
     if (score < bescore){
       bescore = score;besti = i ;}
 }

   if ( besti < 0 )
    {
      stg_star_m = -besti ;stg_fin_m = nucateg + besti  ;
      for (j = 0 ; j <  nucateg; j++){
        if (j < stg_fin_m){
           guich = stg_star_m + j ;
           pt_sp1 = consense_matrix [sp1][j].pt ;
           pt_sp2 = consense_matrix [sp2][j].pt ;
           pt_sp3 = consense_matrix [sp3][guich].pt ;
          // printf("\narriba besti=%i , j=%i , guich=%i",besti,j,guich);
           score= escor_fermat (pt_sp1,pt_sp2,pt_sp3,j,9); }
        else{
          pt_sp1 = consense_matrix [sp1][j].pt ;
          cpy_one (sp1,j) ; }
          }
       }
    else     {
      stg_star_m = besti ;  guich= 0 ;
      for (j = 0 ; j <  nucateg; j++){
        if (j < stg_star_m){
             pt_sp1 = consense_matrix [sp1][j].pt ;
             cpy_one(sp1,j) ;}
         else{
           pt_sp1 = consense_matrix [sp1][j].pt ;
           pt_sp2 = consense_matrix [sp2][j].pt ;
           pt_sp3 = consense_matrix [sp3][guich].pt ;
          // printf("\nabajo besti=%i , j=%i , guich=%i",besti,j,guich);
           guich++ ;
           score= escor_fermat (pt_sp1,pt_sp2,pt_sp3,j,9);} } }


        dde_cns_mtx ++;

}

void make_asis_menage_trois (int  nucateg,int sp1,int sp2,int sp3){
int  j,     move;
Punktyp * pt_sp1, * pt_sp2, * pt_sp3 ;

double score  ;
move =  0 ;
      for (j=0 ; j < nucateg ; j ++){
           pt_sp1 = consense_matrix [sp1][j].pt ;
           pt_sp2 = consense_matrix [sp2][j].pt ;
           pt_sp3 = consense_matrix [sp3][j].pt ;
           score= escor_fermat (pt_sp1,pt_sp2,pt_sp3,j,9);}
           dde_cns_mtx ++;
}




void cpy_one (int sp,int cat){
int l;
for ( l = 0 ; l< LANDS ; l ++){
       consense_matrix[dde_cns_mtx][cat].pt[l].x = consense_matrix[sp][cat].pt[l].x ;
       consense_matrix[dde_cns_mtx][cat].pt[l].y = consense_matrix[sp][cat].pt[l].y ;
       consense_matrix[dde_cns_mtx][cat].pt[l].z = consense_matrix[sp][cat].pt[l].z ;}
}



void build_extended_states(int nuspecs, int nucateg){
int a,b,c, son = 0 ;
for (a= 0 ; a < nuspecs ; a ++){
 for (b= a ; b < nuspecs ; b ++){
    if (a == b) continue ;
     for (c= b ; c < nuspecs ; c ++){
       if (a==c || b==c) continue ;
    make_asis_menage_trois (nucateg,a,b,c)  ;
    son++;
     }}}
 }




void fill_sankoff_costs(nuspecs,nucateg) {
int a,b ;
  if (!cost_ends) {
   make_d_stretchs_recat () ;
    make_inv_stretchs_recat () ;
    make_shift_stretchs_recat() ;}
  for( a = 0 ; a < STATES  ;a ++ )  
   for ( b = 0 ; b < STATES  ;b ++ ){ 
      if (a == b ) continue ;
        if (doshift)  make_d_shifts  (a,b,nucateg) ;
        if (cost_ends){
          if (dostre)    make_stretch (a,b,nucateg,STATES);
          if (doinvstre) make_stretch_inv (a,b,nucateg,STATES);
          if (doshstre)  make_sh_str (a,b,nucateg,STATES);}
       }
}



int calculate_nustates(nuspecs){
 int a,b,c,vamos=0 ;
 for (a= 0 ; a < nuspecs ; a ++){
  for (b= a ; b < nuspecs ; b ++){
      if (a == b ) continue ;
    for (c= b ; c < nuspecs ; c ++){
      if (a== c || b == c ) continue  ;
      vamos = vamos + 1  ; }}}
 return (vamos + nuspecs);
 }

int correct_triangle_inequality (  ) {
    int a,b,c, viol=0 ;
    double disA,disB,disC ;
    for (a = 0 ; a < STATES ; a ++ )
     {
      for (b = a +1 ; b < STATES ; b ++ )
      {
        for (c = b +1 ; c < STATES ; c ++ )
        {
         // printf("%i,%i,%i-",a,b,c);
          disA = sank_mtx[a][b].best_overall ;
          disB = sank_mtx[b][c].best_overall ;
          disC = sank_mtx[a][c].best_overall ;
          if ((disA + disB)  < disC ){
            sank_mtx[a][c].best_overall = disA+disB ;
            sank_mtx[c][a].best_overall = disA+disB ;
             viol++ ;
            }
          if ((disC + disA)  < disB ){
            sank_mtx[b][c].best_overall = disA+disC ;
            sank_mtx[c][b].best_overall = disA+disC ;
             viol++ ;
            }
          if ((disC + disB)  < disA ){
            sank_mtx[a][b].best_overall = disC+disB ;
            sank_mtx[b][a].best_overall = disC+disB ;
            viol++ ;}
         }
       }
     }
  if (viol == 0 ){
     //printf("\ncorrect NO VIOLATION OF TRIANGLE INEQUALITY!!!!");
      return ( 0 ); }
  else{
      printf("\nVIOLATION OF TRIANGLE INEQUALITY");
      return (1);     }


  }



int test_triangle_inequality (  ) {
   int a,b,c, viol=0 ;
    double disA,disB,disC ;
    for (a = 0 ; a < STATES ; a ++ ) {
      for (b = a +1 ; b < STATES ; b ++ ){
        for (c = b +1 ; c < STATES ; c ++ ){
          disA = sank_mtx[a][b].best_overall ;
          disB = sank_mtx[b][c].best_overall ;
          disC = sank_mtx[a][c].best_overall ;
         if ( ((disA + disB)  < disC ) || ((disC + disB)  < disA ) || ((disC + disA)  < disB )){
          printf("\nVIOLATION OF TRIANGLE INEQUALITY AMONG STATES %i,%i,%i, ", a,b,c );
          viol ++ ; } } } }

  if (viol != 0 ){
      //printf("\n test VIOLATION OF TRIANGLE INEQUALITY ");
  return (1) ;
  }
  else{
    //printf("\n test no VIOLATION OF TRIANGLE INEQUALITY ");
   return (0); }
  }



double tmp_score (int sp1,int internal,int move,int cual){
int  c, l,stg_star_m, guich, j,stg_fin_m,i;
double score=0, totscore = 0, esco =0  ;
Punktyp * pts_sp1, * pts_sp2 ;
    if ( move < 0 ) { // si en la rama hay un shift negativo
             i =  move ;
             stg_star_m = -i ;stg_fin_m = NUCATEG + i  ;
              for (j = 0 ; j <  NUCATEG; j++)
               {
               if (j < stg_fin_m)
                {
                guich = stg_star_m + j ;
                pts_sp1 = buff_traj [cual][j].pt ;
                pts_sp2 = optimus_matrix [sp1][guich].pt ;
                esco = pair_conf_dist (pts_sp1,pts_sp2);
                score = score + esco ;
                        }
               }
            l = -i ;

            score = score /  (NUCATEG - l) ;
            score = score + ( penalty * l) ;
           }
        else
         if (  move == 0 ){ // si no hay shift en la rama
          for ( c = 0  ; c < NUCATEG ; c ++){
            pts_sp1 = buff_traj[cual][c].pt ;
            pts_sp2 = optimus_matrix [sp1] [c].pt ;
            score+= pair_conf_dist (pts_sp1,pts_sp2);}
            score = score / NUCATEG;
         }
          else{ //si hay shift positivo en la rama
              stg_star_m = move ;  guich= 0 ; score=0;
              for (j = 0 ; j <  NUCATEG; j++)
                {
                if (j >= stg_star_m){
                 pts_sp1 = buff_traj[cual][j].pt ;
                 pts_sp2 = optimus_matrix [sp1][guich].pt ;
                 guich++ ;
                 score += pair_conf_dist (pts_sp1,pts_sp2);}
                 }
              score = score / ( NUCATEG - move );
              score = score + ( penalty * move) ;
               }
    totscore+= score ;
    trece = 0 ; dos = 0 ;
return(totscore);
 }


double score_by_branch (int asis){
int n ,d, c, l,stg_star_m, guich,des, anc,nodo,j,stg_fin_m,i, st_der, st_anc;
double score, totscore = 0, core, esco=0    ;
Punktyp * pts_sp1, * pts_sp2 ;

for ( n = 0 ; n < intnods ; n ++){
    nodo = optlist [n] ;
    for (d = firs[nodo] ; d != - 9  ; d = sis [ d  ] )
    {
       score = 0 ;
       des = d ; anc = nodo ;
       if ( asis )
         {
          for ( c = 0  ; c < NUCATEG ; c ++){
            pts_sp1 = optimus_matrix [anc][c].pt ;
            pts_sp2 = optimus_matrix [des] [c].pt ;
            score+= pair_conf_dist (pts_sp1,pts_sp2);}
            score = score / NUCATEG;}
     else{
       if ( ( position[des] - position[anc] ) < 0 ) { // si en la rama hay un shift negativo
             i =  position[des] - position[anc] ;
             stg_star_m = -i ;stg_fin_m = NUCATEG + i  ;
              for (j = 0 ; j <  NUCATEG; j++)
               {
               if (j < stg_fin_m)
                {
                guich = stg_star_m + j ;
                pts_sp1 = optimus_matrix [anc][j].pt ;
                pts_sp2 = optimus_matrix [des][guich].pt ;
                esco =  pair_conf_dist (pts_sp1,pts_sp2);
                score = esco + score ;
                }
               }
            l = -i ;
            score = score /  (NUCATEG - l) ;
            score = score + ( penalty * l) ;

           }
        else
         if ( ( position[des] - position[anc] ) == 0 ){ // si no hay shift en la rama
          for ( c = 0  ; c < NUCATEG ; c ++){
            pts_sp1 = optimus_matrix [anc][c].pt ;
            pts_sp2 = optimus_matrix [des] [c].pt ;
            score+= pair_conf_dist (pts_sp1,pts_sp2);}
            score = score / NUCATEG;

           }
          else{ //si hay shift positivo en la rama
              guich= 0 ; score=0;
              stg_star_m = position[des] - position[anc] ;
              for (j = 0 ; j <  NUCATEG; j++)
                {
                if (j >= stg_star_m){
                 pts_sp1 = optimus_matrix [anc][j].pt ;
                 pts_sp2 = optimus_matrix [des][guich].pt ;
                 guich++ ;
                 score += pair_conf_dist (pts_sp1,pts_sp2);}
                 }
              score = score / ( guich);
              score = score + ( penalty * stg_star_m ) ;
               }
     }
    brnch_scor [des] = score ;
    totscore+= score ;
    }

  }

    core = 0;

 sank_file= fopen("sankofff.out", "a");

    for ( n = 0 ; n < intnods ; n ++)
    {
      nodo = optlist [n] ;
      for (d = firs[nodo] ; d != - 9  ; d = sis [ d  ] ){
        st_anc = recons[ 0 ][ nodo ] ;
        if (d < nt )
         st_der = d ;
        else
         st_der = recons[ 0 ][ d ] ;
        core = core + sank_mtx[st_anc][st_der].best_overall ;
        if (!asis)
          fprintf(sank_file,"\n score nodo %i sank/branchTNT  %f/%f",d,sank_mtx[st_anc][st_der].best_overall,brnch_scor[d]);
        else
          fprintf(sank_file,"\n score nodo %i sank/branchTNT  %f/%f",d,sank_mtx[st_anc][st_der].score_asis,brnch_scor[d]); }}
fclose(sank_file);


return(totscore);

 }//score_by_branch()


int all_desc (nodo){
int d ;
  if (nodo >= nt ){
    for ( d = firs [ nodo ] ; d >= 0 ; d = sis [ d ] )
         all_desc ( d ) ; }
  desc [dde] = nodo ;
  dde ++ ;
return (dde) ;
}



generate_tps_asis () {
int a,l,c ;
Punktyp * pt ;
outputFilename [0] = NULL;
strcpy(outputFilename,prefix);
strcat(outputFilename, "_trajectories.tps");

output_file= fopen(outputFilename, "w");


for (a=0 ; a < nnods; a++ ) {
 for (c=0 ; c < NUCATEG; c++ ) {
   if (DIMS == 3 )
     fprintf(output_file,"LM3=%i\n",LANDS) ;
   else
     fprintf(output_file,"LM=%i\n",LANDS) ;
   pt = optimus_matrix[a][c].pt ;
   for (l= 0 ; l < LANDS; l++){
     if (DIMS == 3 )
       fprintf(output_file,"%f %f %f\n",pt->x ,pt->y,pt->z) ;
     else
       fprintf(output_file,"%f %f\n",pt->x ,pt->y);
     pt++;  }
   if (a < nt)
     fprintf(output_file,"ID=%s_Stg_%i\n",sps_list[ a].sps_name,c);
   else
   fprintf(output_file,"ID=IntNod_%i_Stg_%i\n",nod_p2t[a],c);

    }
   }
fclose(output_file);
}


void generate_tps_terms (int nucateg) {
int a,l,c ;
Punktyp * pt ;
outputFilename[0] = NULL;
 strcat (outputFilename,prefix);
sprintf(outputFilename, "trajectories.tps");
output_file= fopen(outputFilename, "w");

for (a=0 ; a < nuspecs; a++ ) {
 for (c=0 ; c < nucateg; c++ ) {
   pt = align_matrix[a][c].pt ;
   if (pt->x == -10000001)
    continue ;
    if (DIMS == 3 )
     fprintf(output_file,"LM3=%i\n",LANDS) ;
   else
     fprintf(output_file,"LM=%i\n",LANDS) ;
   for (l= 0 ; l < LANDS; l++){
     if (DIMS == 3 )
       fprintf(output_file,"%f %f %f\n",pt->x ,pt->y,pt->z) ;
     else
       fprintf(output_file,"%f %f\n",pt->x ,pt->y);
     pt++;  }
   if (a < nt)
     fprintf(output_file,"ID=%s_Stg_%i\n",sps_list[ a].sps_name,c);
   else
   fprintf(output_file,"ID=IntNod_%i_Stg_%i\n",a,c);

    }
   }
fclose(output_file);
}


generate_tps_recat (int nuteg) {
int a,l,c ;
Punktyp * pt ;
outputFilename[0] = NULL;
strcat (outputFilename,prefix);
strcat(outputFilename, "_trajectories.tps");
output_file= fopen(outputFilename, "w");

;

for (a=0 ; a < nnods; a++ ) {
 for (c=0 ; c < nuteg; c++ ) {
   pt = optimus_matrix[a][c].pt ;
   if (mask_aln[a][c] == 0 )
    continue ;
    if (DIMS == 3 )
     fprintf(output_file,"LM3=%i\n",LANDS) ;
   else
     fprintf(output_file,"LM=%i\n",LANDS) ;
   for (l= 0 ; l < LANDS; l++){
     if (DIMS == 3 )
       fprintf(output_file,"%f %f %f\n",pt->x ,pt->y,pt->z) ;
     else
       fprintf(output_file,"%f %f\n",pt->x ,pt->y);
     pt++;  }
   if (a < nt)
     fprintf(output_file,"ID=%s_Stg_%i\n",sps_list[ a].sps_name,c);
   else
   fprintf(output_file,"ID=IntNod_%i_Stg_%i\n",nod_p2t[a],c);

    }
   }
fclose(output_file);
}





void generate_tps_shift (int nuteg) {
int a,l,c,i ;
Punktyp * pt ;
outputFilename[0] = NULL;
strcat (outputFilename,prefix);
strcat (outputFilename,"_trajectories.tps");
output_file= fopen(outputFilename, "w");

for (a=0 ; a < nnods; a++ ) {
 for (c=0 ; c < nuteg; c++ ) {
   if (mask_aln [a][c])
     {
      for ( i = 0  ; i < NUCATEG;  i ++ )
      {
        pt = optimus_matrix[a][i].pt ;
       if (DIMS == 3 )
         fprintf(output_file,"LM3=%i\n",LANDS) ;
       else
         fprintf(output_file,"LM=%i\n",LANDS) ;
       for (l= 0 ; l < LANDS; l++)
        {
         if (DIMS == 3 )
          fprintf(output_file,"%f %f %f\n",pt->x ,pt->y,pt->z) ;
         else
          fprintf(output_file,"%f %f\n",pt->x ,pt->y);
          pt++;
         }
         if (a < nt)
          fprintf(output_file,"ID=%s_Stg_%i\n",sps_list[ a].sps_name,c+i);
        else
         fprintf(output_file,"ID=IntNod_%i_Stg_%i\n",nod_p2t[a],c+i);
        }
      break ;}
    }

 }
fclose(output_file);
}


generate_covariate_recat (int nuteg) {
int a,c, t, son,i ;
double age, pace ;
sprintf(outputFilename, "covariate_heter.txt");
output_file= fopen(outputFilename, "w");


fprintf(output_file,"ID,Stage,CS\n");

for (a=0 ; a < nnods; a++ )
{
 for (c=0 ; c < nuteg  ; c++ )
 {
   son = sup_limit_cont[a] - inf_limit_cont [a]  ;
   pace = (max_cont[a] - min_cont[a])  / (son - 1 ) ; //min_cont y max_cont son leidos de la optimizacion de tnt. TNT lee de los terminales el promedio de age para todos los individuos de la categoria final e inicial

   if (mask_aln[a][c] == 1 )
   {i = 0 ;
    for (t =  c;  t < (c + son ) ; t ++, i++ ) {
      age = min_cont[a]  + (i * pace);
      if (a < nt)
       fprintf(output_file,"%s_Stg_%i,%i,%f\n",sps_list[ a].sps_name,t,t,age);
      else
       fprintf(output_file,"IntNod_%i_Stg_%i,%i,%f\n",nod_p2t[a],t,t,age);
       }
     break ;
   }
  }
 }
fclose(output_file);

if (doasisfiles){
 sprintf(outputFilename, "covariate_asis.txt");
 output_file= fopen(outputFilename, "w");
 fprintf(output_file,"ID,Stage,CS\n");
 for (a=0 ; a < nnods; a++ )
 {
  pace = (max_cont[a] - min_cont[a]) / (NUCATEG - 1 )  ;
  for (c=0 ; c <( NUCATEG )  ; c++ )
  {
   age = min_cont[a]  + (c * pace);
     if (a < nt)
       fprintf(output_file,"%s_Stg_%i,%i,%f\n",sps_list[ a].sps_name,c,c,age);
      else
       fprintf(output_file,"IntNod_%i_Stg_%i,%i,%f\n",nod_p2t[a],c,c,age);
       }
  }
 fclose(output_file);
 }

}




void generate_species_classif_recat (int nuteg) {
int a,c ;
Punktyp * pt ;
sprintf(outputFilename, "classif_hete.txt");
output_file= fopen(outputFilename, "w");
fprintf(output_file,"ID,Especie\n");

for (a=0 ; a < nnods; a++ ) {
 for (c=0 ; c < nuteg; c++ ) {
   pt = optimus_matrix[a][c].pt ;
   if (mask_aln[a][c] == 0 )
    continue ;
   if (a < nt)
     fprintf(output_file,"%s_Stg_%i,%s\n",sps_list[ a].sps_name,c,sps_list[ a].sps_name);
   else
   fprintf(output_file,"IntNod_%i_Stg_%i,IntNod_%i\n",nod_p2t[a],c,nod_p2t[a]);
      }
 }
fclose(output_file);

if ( doasisfiles){
sprintf(outputFilename, "classif_asis.txt");
output_file= fopen(outputFilename, "w");
fprintf(output_file,"ID,Especie\n");

for (a=0 ; a < nnods; a++ ) {
 for (c=0 ; c < NUCATEG; c++ ) {
   if (a < nt)
     fprintf(output_file,"%s_Stg_%i,%s\n",sps_list[ a].sps_name,c,sps_list[ a].sps_name);
   else
    fprintf(output_file,"IntNod_%i_Stg_%i,IntNod_%i\n",nod_p2t[a],c,nod_p2t[a]);
      }
 }
}
fclose(output_file);

}









int resample (int nuspecs, int nucategs, int extended){
int n, yeso, opt_asis,a,b , i, r;
double newscore ;

for (n=0 ; n < nnods ; n++)
  trans_freq [ n ] = 0  ;

conf_x_categ (nuspecs,nucategs ) ;
for (i = 1 ; i < (replications + 1)  ; i ++){
  fill_consense_matrix_resample(nuspecs,nucategs,i) ;
  dde_cns_mtx =nuspecs ;
 if (extended)
    build_extended_states(nuspecs, NUCATEG) ;
  max_modif = calculate_max_modif (NUCATEG,nuspecs) ;
  for( a = 0 ; a < STATES  ;a ++ )
    for ( b = 0 ; b < STATES  ;b ++ ){
      if (a == b ) continue ;
         make_as_is (a,b,NUCATEG,STATES) ;}
  fill_sankoff_costs(nuspecs,NUCATEG) ;
  put_best_score (NUCATEG) ;
  triangle_ineq () ;
  yeso=0  ;  opt_asis = 0;
  sank_downpass () ;
  sank_uppass () ;
  newscore= fill_reconstructions_new (nt) ;

 
   map_changes (0,i) ;}

for (n=0 ; n < nnods ; n++) {
 for (r=0 ; r < replications ; r++) {
  if (n == nt) continue;
   if ( transform_rnd [ n ] [ r ]  == transformations [ n ]  )
      if ( guich_map [n] == guich_rnd [n][r] )
        trans_freq [ n ] ++ ;}}
for (n=0 ; n < nnods ; n++)
  trans_relf[n]= ( (double)trans_freq[n]/replications) * 100 ;

return (1) ;
}

void conf_x_categ (int espe, int cates ){
int a , j, i ,k;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_conf = datamatrix ;
pt_sp = sps_list ;



for  ( a = 0 ; a < espe ; a ++ )
 for (j= 0 ;  j < cates  ; j ++)
   nuconf_sp_clas [a][j] = 0  ;
for  ( a = 0 ; a < espe ; a ++ ){
 for (j= 0 ;  j < cates  ; j ++){
  for (i = 0 ;  i < pt_sp[ a ].num_confs  ; i ++){
   k = pt_sp[ a ].conflist[ i ] ;
   if ( pt_conf [k].which_class == j )
       nuconf_sp_clas [a][j] ++ ; }}}
}



void jusout () {
int izq , der,son ;
izq= firs[ nt] ;
der = sis[izq] ;

 son = all_desc (izq);
 if (son ==1){
  OUTGRP = izq ;
  return ;}
 son = all_desc (der);
 if (son == 1){
  OUTGRP = der ;
  return ;}
 if (der < izq ){
    OUTGRP = der ;
    return ; }
  else {
    OUTGRP = izq ;
    return ; }


}


void fill_consense_matrix_resample ( int espec, int nucats,int vta){
int i, j ,k,  nulan, l,  son , a, valor ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
Punktyp * conma ;
pt_conf = datamatrix ;
pt_sp = sps_list ;
nulan = LANDS ;


for  ( a = 0 ; a < espec ; a ++ )
  {
    for (j= 0 ;  j < nucats  ; j ++)
    {
      conma = consense_matrix [ a ][ j ].pt;
      for (l = 0 ; l < nulan ; l++){
        conma->x = 0; conma->y = 0;conma->z = 0; conma++ ; }
      son = 0 ;
      if ( nuconf_sp_clas[a][j] == 1 )
        {
         for (i = 0 ;  i < pt_sp[ a ].num_confs  ; i ++){
          k = pt_sp[ a ].conflist[ i ] ;
          if ( pt_conf [k].which_class == j )
          {
            conma = consense_matrix [a][j].pt;
           for (l = 0 ; l < nulan ; l++){
             conma->x  +=pt_conf[k].pt[l].x ;
             conma->y  +=pt_conf[k].pt[l].y;
             conma->z  +=pt_conf[k].pt[l].z;
             conma++; }}  }
          break ;
         }
      else
       {
        while (son == 0 )
        {
         for (i = 0 ;  i < pt_sp[ a ].num_confs  ; i ++)
         {
          k = pt_sp[ a ].conflist[ i ] ;
          if ( pt_conf [k].which_class == j )
          {
           valor = valor = rand() % 100 ;
            if (valor < 25 )
              continue ;
            conma = consense_matrix [a][j].pt;
            for (l = 0 ; l < nulan ; l++){
              conma->x  +=pt_conf[k].pt[l].x ;
              conma->y  +=pt_conf[k].pt[l].y;
              conma->z  +=pt_conf[k].pt[l].z;
              conma++; }
            son ++;
          }
        }
      }
      conma = consense_matrix [a][j].pt;
      for (l = 0 ; l < nulan ; l++){
          conma->x  =  conma->x  / son ;
          conma->y  =  conma->y  / son ;
          conma->z  =  conma->z  / son ; conma++ ;}
      }
   }
 }
return ;
}  //fill_consense_matrix


void optimize_tree_asis (int doal) {
    int n ,  st_der,st_anc, d, nodo;

if (recons != NULL)
  dealloc_recons () ;
opt_asis = 1 ;
if (!skip_optim){
 scor_AS_FS= sank_downpass () ;
 sank_uppass () ;
 scor_AS_reco= fill_reconstructions_new (nt) ;}


/* ACA GENERA EL ALINEAMIENTO AS IS */
generate_alignment_asis (NUCATEG,nuspecs ) ;
my_spawn_asis  (   ) ;
//remove ( asisFilename );
input_file = fopen ("trans.tmp","rb") ;
generate_nodtrans () ;
fclose (input_file) ;// lee el tmp para traducir los nodos
if (!read_tmp_data ( NUCATEG,1  )){
    printf("\nLa cagamos Carlos");

     return; }
remove ("tmp_asis.tmp");
remove ("asis_2tnt.tmp");
remove ("asis_2pasos.tmp");
remove ("trans.tmp");



/* showachange sirve para ver el cambio entre dos nodos pueden ser terminales o nodos internos solo que tiene q ser solo con !doall */
//showachange (ances,desce,stg_asis,stg_ancH,stg_desH,1) ; // aca imprime en el archivo las configs optimizadas desde TNT como asis
if (!doal)
 scor_AS_TNT = score_by_branch (1 ) ; // uno quiere decir que usa as is
fclose (input_file) ;
generate_tps_asis () ;
core = 0 ;
    for ( n = 0 ; n < intnods ; n ++)
    {
      nodo = optlist [n] ;
      for (d = firs[nodo] ; d != - 9  ; d = sis [ d  ] ){
        st_anc = recons[ 0 ][ nodo ] ;
        if (d < nt )
         st_der = d ;
        else
         st_der = recons[ 0 ][ d ] ;
        core = core + sank_mtx[st_anc][st_der].score_asis ;
         }}

 } //optimize_tree_asis


int optimize_tree_hetero(int doal )
{
double  newscore;
 opt_asis = 0;
 if (!skip_optim){
   scor_H_FS= sank_downpass () ;
   sank_uppass () ;
   newscore= fill_reconstructions_new (nt) ;}
 map_changes (0,0) ; // aca agrega a branch_labels las tranformaciones q obtiene de transformations

   // va a hacer alineamientos en todos los casos excepto que sea discreto e infiera stretchs.
  WAT_CHG = r_stretchs (0 ) ;
 if (  WAT_CHG == 0  )  // si no hay mov  sean como sean los datos
       cat_alin = generate_alignment_shift ( 0,NUCATEG,nuspecs,WAT_CHG,timeas ) ; //en generate alignment new y generate_alignment_asis se generan archivos para q los lea TNT
 else if ( WAT_CHG  == 1  ) // si hay solo shift sean como sean los datos
    cat_alin = generate_alignment_shift ( 0,NUCATEG,nuspecs,WAT_CHG,timeas ) ; //en generate alignment new y generate_alignment_asis se generan archivos para q los lea TNT
 else if ( WAT_CHG  == 2  )
        if (timeas){
         cat_alin = generate_alignment_recat (0,WAT_CHG) ;}
return (cat_alin) ;
}


int r_stretchs (int qreco ) {
int n, std_anc,std_nod, shif = 0  ;
Sank_spcelltyp ** pt_sank ;
pt_sank = sank_mtx;

 for (n =  0 ; n < nnods ; n++ ){
     if (n == nt ) continue ;
   std_anc = recons[ qreco ][ ances[n] ];
   if ( n < nt )
      std_nod = n  ;
   else
    std_nod = recons[ qreco ][ n ];
   if ( pt_sank[std_anc][std_nod].what_best == 1)
      shif ++ ;
   if ( ( pt_sank[std_anc][std_nod].what_best == 2) || (pt_sank[std_anc][std_nod].what_best == 3) ||  (pt_sank[std_anc][std_nod].what_best == 4 ) )
      return (2) ;     }
 if (shif > 0 )
  return (1) ;
 else
  return (0) ;
}


void define_limit_stretch  ( int cto,int nucats, int especie ) {
int lims,  j   ;
double span ;
lims = nucats + 1  + cto ;
span = (sps_list[especie].max_age -  sps_list[especie].min_age ) / ( lims - 1 );

// cuando el cto es positivo genero un limite de mas, no problem


for (j = 0 ; j < lims    ; j ++ ){
   limits_str  [j] = sps_list[especie].min_age  + ( span * j ) ;
     /* printf ("\n limite_str %i = %f", j , limits_str[j] ) ;*/ }
}

void define_limit_db_stretch  ( int cto,int nucats, int especie,int fin ) {
int lims,  j   ;
double span ;
lims = nucats + 1  - cto + fin;  //ver si cto es neg implica mas a la derecha mientras q si fin es neg bajan el numero de cats.
span = (sps_list[especie].max_age -  sps_list[especie].min_age ) / ( lims - 1 );

// cuando el cto es positivo genero un limite de mas, no problem


for (j = 0 ; j < lims    ; j ++ ){
   limits_str  [j] = sps_list[especie].min_age  + ( span * j ) ;
     /* printf ("\n limite_str %i = %f", j , limits_str[j] ) ;*/ }
}




int sorting_confs_in_cats_stretch (int nucats, int nusp, int nuconf, int especie, int cto, int invertido ){
int  j , cual=0, k,edad ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_conf = datamatrix ;
pt_sp = sps_list ;

if (invertido == 2)
  nucats = nucats + cto ;
if (invertido == 1  )
    nucats = nucats + cto ;
if ( invertido == 0  )
  nucats = nucats + cto ;  // cto es negativo bajan el numero de categs a llenar deberia ser

 //con invertido y cto negativo se deben mantener las categs.

for (j = 0 ;  j <  nucats     ; j ++)
  yes_str [j] = 0   ;
for (j = 0 ;  j <  nuconf     ; j ++)
  pt_conf [j].which_str_class = -1 ;



for (j = 0 ;  j < pt_sp [ especie ].num_confs  ; j ++)
        {
          cual = pt_sp [especie].conflist [j] ;
          for (k = 0 ;  k < nucats    ; k ++)
          {
           if (timeas)
            {
             if ( k == 0  )
              {
               if ( ( pt_conf[cual].age >= limits_str[k] ) && (pt_conf[cual].age <= limits_str [k+1] ) )
                 {
                  yes_str [k] = 1 ;
                  pt_conf[cual].which_str_class = k ;
                 }
              }
             else
              if ( ( pt_conf[cual].age > limits_str[k] ) && (pt_conf[cual].age <= limits_str [k+1] ) )
              {
               yes_str [k] = 1 ;
               pt_conf[cual].which_str_class = k ;
              }
            }
           else
            {
             edad = pt_conf[cual].age ;
             if (  edad  ==  k )
             {
              yes_str[k] = 1 ;
              pt_conf[cual].which_str_class = k ;}
             }
          }
        }

   for (j = 0 ;  j < nucats  ; j ++)
     if (yes_str [j] == 0 ){
      /*printf("\nStretch %i in sp %i cannot be done given the lack of data",especie, cto);
      printf("\nNo obs for cat %i (%f-%f) species %i",j,limits_str[j],limits_str[j+1],especie);
      printf("\n") ;*/
      return (0) ;}


       return (1);
} // sorting_confs_in_cats_stretch

int fill_w_consense_stretch (int cto, int nucats,  int especie_to_str, int invertido, int chgend ) {
int i, j ,  nulan, l,  son,  conf, cual,start,finish  ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_conf = datamatrix ;
pt_sp = sps_list ;
nulan = datamatrix[0].nulands ;
for (i = 0 ;  i < nucats  ; i ++)
  dock2[i].pt[0].x = - 10000001 ;

if (invertido == 0){  // cuando no es invertido se cargan todas las categorias de stretch empezando en cero. Si es positivo el stretch se cargan todas las categs originales no las de stretch
 start = 0 ;
 if (cto < 0)
  finish = nucats + cto ;//si cto es negativo y no es invertido bajan el numero de categs
 else
  finish = nucats ;       // cargo solo las primeras las que sobran no las cargo
 for (j = start ;  j < finish  ; j ++)
 {
   for (l = 0 ; l < nulan ; l++){
     buff_dock[0].pt[l].x = 0;  buff_dock[0].pt[l].y = 0; buff_dock[0].pt[l].z = 0 ;}
   son = 0 ;
   for (i = 0 ;  i < pt_sp[ especie_to_str ].num_confs  ; i ++)
    {
     conf =  pt_sp[ especie_to_str ].conflist[i] ;
      if ( pt_conf [conf].which_str_class == j ) {
          for (l = 0 ; l < nulan ; l++){
            buff_dock[0].pt[l].x  +=pt_conf[conf].pt[l].x ;
            buff_dock[0].pt[l].y  +=pt_conf[conf].pt[l].y;
            buff_dock[0].pt[l].z  +=pt_conf[conf].pt[l].z;  }
         son ++ ;}
    }

    for (l = 0 ; l < nulan ; l++){
        dock2[j].pt[l].x = buff_dock[0].pt[l].x / son ;
        dock2[j].pt[l].y = buff_dock[0].pt[l].y / son ;
        dock2[j].pt[l].z = buff_dock[0].pt[l].z / son ;}

   }
  }
  else
   if (invertido == 1 ) // si es invertido aca nucats es el numero de cats originales.
   {
     if (cto < 0 ) {  // cuando el mov es negativo achico el numero de cats del modificado y comparo con un numero reducido de la referencia. Ademas empieza al final de la trayect
      cual = 0 ;   start = - cto   ; finish = nucats ;  }
     else{
      cual = cto ; start = 0 ; finish = nucats ; //cuando es positivo compara todas las categs del referencia con las del modificado excepto las mas bajas q son las que quedas afuera
        }

     for (j = start ;  j <  finish   ; j ++)
     {
      for (l = 0 ; l < nulan ; l++){
       buff_dock[0].pt[l].x = 0;  buff_dock[0].pt[l].y = 0; buff_dock[0].pt[l].z = 0 ;}
       son = 0 ;
     for (i = 0 ;  i < pt_sp[ especie_to_str ].num_confs  ; i ++)
     {
      conf =  pt_sp[ especie_to_str ].conflist[i] ;
      if ( pt_conf [conf].which_str_class == cual ) {
          for (l = 0 ; l < nulan ; l++){
            buff_dock[0].pt[l].x  +=pt_conf[conf].pt[l].x ;
            buff_dock[0].pt[l].y  +=pt_conf[conf].pt[l].y;
            buff_dock[0].pt[l].z  +=pt_conf[conf].pt[l].z;  }
         son ++ ;}}
     for (l = 0 ; l < nulan ; l++){
         dock2[j].pt[l].x = buff_dock[0].pt[l].x / son ;
         dock2[j].pt[l].y = buff_dock[0].pt[l].y / son ;
         dock2[j].pt[l].z = buff_dock[0].pt[l].z / son ;}
     cual ++;}
    }
    else{
     if (invertido == 2 ){
      if (cto < 0 ) {    // cual hace referencia a cual categoria de la modificada
       cual = -cto ;   start = 0   ;}
      else{
        cual = 0 ; start = cto ;}
      if (chgend < 0 ) {
           finish = nucats + chgend   ;}
       else{
          finish = nucats ;  }
       }//cuando es positivo compara todas las categs del referencia con las del modificado excepto las mas bajas q son las que quedas afuera
       for (j = start ;  j <  finish   ; j ++)
        {
        for (l = 0 ; l < nulan ; l++){
         buff_dock[0].pt[l].x = 0;  buff_dock[0].pt[l].y = 0; buff_dock[0].pt[l].z = 0 ;}
        son = 0 ;
        for (i = 0 ;  i < pt_sp[ especie_to_str ].num_confs  ; i ++)
        {
        conf =  pt_sp[ especie_to_str ].conflist[i] ;
         if ( pt_conf [conf].which_str_class == cual ) {
          for (l = 0 ; l < nulan ; l++){
            buff_dock[0].pt[l].x  +=pt_conf[conf].pt[l].x ;
            buff_dock[0].pt[l].y  +=pt_conf[conf].pt[l].y;
            buff_dock[0].pt[l].z  +=pt_conf[conf].pt[l].z;  }
         son ++ ;}}
        for (l = 0 ; l < nulan ; l++){
        dock2[j].pt[l].x = buff_dock[0].pt[l].x / son ;
        dock2[j].pt[l].y = buff_dock[0].pt[l].y / son ;
        dock2[j].pt[l].z = buff_dock[0].pt[l].z / son ;}
     cual ++;}}
return(0 );
}

double score_in_docks (int nucats, int quehago, int invertido, int chgend )
 {
  Punktyp *  pt_cf1, * pt_cf2  ;
  int  j ,  pairs = 0 , start, finish;
  double totscore = 0 , escore = 0 ; ;
 // invertido 0 = stretch, invertido=1 str inv;invertido = 2 db stretch
  if (quehago >= 0)
  {
   start = 0 ;
   if (invertido == 1){
      finish = nucats  ;}
    else
      if (invertido == 0 ){
       finish = nucats ;  }
      else // invertido == 2 ver si esto esta bien
       {
        start = quehago ;
        if (chgend >0)
         finish = nucats  ;
        else
         finish = nucats + chgend ;
       }
     for (j = start; j <  finish ; j++ ){
      pt_cf1 = dock1[j].pt ;
      pt_cf2 = dock2[j].pt ;
      if ( ( pt_cf1[0].x != -10000001) && ( pt_cf2[0].x != -10000001)  ) {
        escore = pair_conf_dist ( pt_cf1 , pt_cf2 ) ;

        totscore = escore + totscore ;
        pairs++ ; }
        }
  }
  else { // quehago < 0
      if (invertido == 1 ){
         start = - quehago   ; finish = nucats   ;   }
      else
        if (invertido== 0 ) {
         start = 0 ; finish = nucats + quehago ; }
        else{ //invertido == 2  ver si esto esta bien
            start = 0  ;
         if ( chgend < 0 ) //
          finish = nucats + chgend ;
         else
          finish = nucats ; }

      for (j = start; j <  finish ; j++ ) {
        pt_cf1 = dock1[j].pt ;
        pt_cf2 = dock2[j].pt ;
       if ( ( pt_cf1[0].x != -10000001) && ( pt_cf2[0].x != -10000001)  ) {
        escore = pair_conf_dist ( pt_cf1 , pt_cf2 ) ;
   
        totscore = escore + totscore ;
        pairs++ ;}}
  }


 totscore = totscore / pairs ;
 return ( totscore )   ;
 }

void fill_doc1_w_consense_asis ( int guichsp, int nucats  ){
int i, j ,  nulan, l,  son, k ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_conf = datamatrix ;
pt_sp = sps_list ;
nulan = datamatrix[0].nulands ;
for (i = 0 ;  i < nucats  ; i ++)
   dock1[i].pt[0].x = - 10000001 ;

//printf("\nvalores consens as is\n");
for (j= 0 ;  j < nucats  ; j ++)
  {
   for (l = 0 ; l < nulan ; l++){
     buff_dock[0].pt[l].x = 0;  buff_dock[0].pt[l].y = 0; buff_dock[0].pt[l].z = 0;
     }
   son = 0 ;
   for (i = 0 ;  i < pt_sp[guichsp].num_confs  ; i ++)
    {
        k = pt_sp[guichsp].conflist[i] ;
        if ( pt_conf [k].which_class == j ) {
         for (l = 0 ; l < nulan ; l++){
            buff_dock[0].pt[l].x  +=pt_conf[k].pt[l].x ;
            buff_dock[0].pt[l].y  +=pt_conf[k].pt[l].y;
            buff_dock[0].pt[l].z  +=pt_conf[k].pt[l].z;  }
         son ++ ;}
    }
      for (l = 0 ; l < nulan ; l++){
        dock1[j].pt[l].x = buff_dock[0].pt[l].x / son ;
        //printf("%i:%.2f ",j,dock1[j].pt[0].x);
        dock1[j].pt[l].y = buff_dock[0].pt[l].y / son ;
        dock1[j].pt[l].z = buff_dock[0].pt[l].z / son ;}

 }

} //fill_doc1_w_consense_asis


void generate_dock ( int catnum ) {
int i, nulan ;
nulan = datamatrix[0].nulands ;
dock1 = (Conftyp * ) malloc ( catnum * sizeof (Conftyp) ) ;
dock2 = (Conftyp * ) malloc ( catnum * sizeof (Conftyp) ) ;
for (i = 0 ; i < catnum ; i ++){
    dock1[i].pt = (Punktyp * ) malloc (nulan * sizeof (Punktyp)) ;
    dock2[i].pt = (Punktyp * ) malloc (nulan * sizeof (Punktyp)) ;}

}

int generate_alignment_recat ( int qreco,int which_cng) {
int  catlin,a , i;
double  range, ranged;

  range = define_d_pairings_recat ( qreco, NUCATEG) ;  //define inf_limit y sup_lmit_cont. El mas chico de todo el alin es 0. aca redondeo too
  ranged = range  ;
  catlin = (int) range ;
  for (a =0; a < catlin + 1  ; a ++ )   // como las configs van a estar en edades alineamiento los limites son directamente los limites de las categs.
    limits_aln_reca [a] =    a ;
  calculate_aln_ages (1) ;   // aca define aln ages entre 0 y la ultima categoria
  sort_configs_aln_recat (catlin) ; // toma en cuenta lo hecho en define... y  calculate_aln_ages
  alloc_alignment (catlin, nt ) ;

  for (i = 0 ;  i < nt ; i ++)
   calculate_consensus_recat (catlin, i) ;
  generate_aln_file (catlin,which_cng) ;
  generate_tmp_file_hetero () ;
  my_spawn_hetero ();
  input_file = fopen ("trans.tmp","rb") ;
  generate_nodtrans () ;
  fclose (input_file) ;// lee el tmp para traducir los nodos
  if (!read_tmp_data_recat(catlin)){
    printf("\nLa cagamos Carlos");

       return (catlin); }
remove("chg_2tnt.tmp");
remove("chg_2pasos.tmp");

 if (dosvg)
   generate_d_svg(catlin,1);
 generate_tps_recat (catlin) ;
  if (do_classif)
    generate_species_classif_recat (catlin) ;
  if (do_covfile){
     generate_age_covariates (catlin) ; // llama a TNT, optimiza y genera un tmp dondestas los cs optimizados
     generate_covariate_recat (catlin) ;}
  return (catlin ) ;
}

int  read_tmp_data_recat(int nucag){ // cuando es recat el tmp_data lee de TNT las configs ancestrales y las en optimus matrix guarda ordenadas como en el alineamiento es decir mantiene las posic.
                                  // cuando es shift (discreto) lo que hace es guardar todo en una matriz sin dejar espacios para los gaps.
    int i, a=0 ,l,b,c, n ;
    char   buffer_tmp [10000] ;
    input_file = fopen ("chg_2pasos.tmp","rb") ; // abre el archivo con las coordenadas ancestrales
    for ( n = 0 ;  n < nnods ;n ++ )
     for ( c = 0 ;  c < nucag ;c ++ )
       mask_aln [n][c] = 0 ;
     for ( n = 0 ;  n < nnods ;n ++ ){
       for ( c = inf_limit_cont[n] ;  c < sup_limit_cont[n] ;c ++ ){
       mask_aln [n][c] = 1 ; } }
    for (a = 0 ; a < 199 ; a ++)
      where [a] = 0 ;
   for (a = 0 ; a < nuspecs ; a ++)
    for (b = 0 ; b < nucag ; b ++)
     for (l = 0 ; l < LANDS ; l ++){
        optimus_matrix [a][b].pt[l].x =  align_matrix[a][b].pt[l].x ;
        optimus_matrix [a][b].pt[l].y =  align_matrix[a][b].pt[l].y ;
        optimus_matrix [a][b].pt[l].z =  align_matrix[a][b].pt[l].z ;}
     for (a = 0 ; a < nucag ; a ++)
           {
            i =  read_next_line ( buffer_tmp) ;
            if ( !i )
             break ;
            if ( strstr(buffer_tmp,"TOTAL" ) != NULL ){
                if (save_configuration_tnt_recat ( a ,  buffer_tmp,0 ) )
                   printf("");
                 else{
                  printf ("\n Error reading tmp data at line %i ", contlin);
                  return (0) ; }
                  }
           }
    fclose (input_file) ;
    remove ("trans.tmp");
      return (1);
}


void generate_tmp_file_hetero ()
{
  output_file= fopen("chg_2tnt.tmp", "w");
  fprintf(output_file,"\n;");
  goto_printree (0) ;
 fprintf(output_file,"\nwarn-;\nsil=all;\nmacro=;\nreport-; \ncls;\ntable/7;\nclb;\ntplot];\n");
 fprintf(output_file,"var: node_fl node_tn ;\nlog trans.tmp ;\n");
 fprintf(output_file,"loop (ntax + 1) nnodes [0]\n set node_fl $$ttag #1 ; set node_tn #1 ; sil-all; if ('node_tn'!=root) quote $node_fl 'node_tn' ; else quote 'node_tn' 'node_tn' ; end;  sil=all;stop ; ");

 fprintf(output_file,"\nlog chg_2pasos.tmp ;\nlm show;\nwarn-;\nsil-all;\n lm ;\n sil=;log/;\n quit ; ");
fclose(output_file);
}  // warn-;


void generate_aln_file(int cats,int which_cng ){
int  l , i , j ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_sp = sps_list ;
pt_conf = datamatrix ;
outputFilename [0] = NULL;
strcat (outputFilename,prefix);
strcat (outputFilename,"_aln.tnt");
strcpy (finalFilename,outputFilename);
output_file= fopen(outputFilename, "w");
fprintf(output_file,"\nmxram 500;");
fprintf(output_file,"\nxread\n%i %i",cats  ,nuspecs);
if (DIMS == 2 )
 fprintf(output_file,"\n&[landmark 2d]");
else
  fprintf(output_file,"\n&[landmark 3d]");
 for ( i= 0 ; i < nuspecs ; i ++)
  {
   fprintf(output_file,"\n%s_%i ",pt_sp[ i ].sps_name,i);
   for ( j= 0 ; j < cats ; j ++)
     {
      if (j != 0)
       fprintf(output_file,"|");
      if ( (align_matrix [i][j].pt[0].x) == -10000001  || ( (!timeas) &&  ( which_cng == 2) ) )  // si tiempo discreto y hay stretchs entonces no ponga ningun land.
      {
       for ( l= 0 ; l < datamatrix[0].nulands ; l ++)
        fprintf(output_file,"? ") ;
      }
      else
       {
        for ( l= 0 ; l < datamatrix[0].nulands ; l ++)
        if (DIMS == 2 )
         fprintf(output_file,"%.6f,%.6f ",align_matrix [i][j].pt[l].x,align_matrix [i][j].pt[l].y);
        else
           fprintf(output_file,"%.6f,%.6f,%.6f ",align_matrix [i][j].pt[l].x,align_matrix [i][j].pt[l].y,align_matrix [i][j].pt[l].z);
       }
     }
   }
fprintf(output_file,"\n;");
fprintf(output_file,"\n");
fclose (output_file) ;
 }

double define_d_pairings_recat (int qreco,int nucas){
int n ,nodo, d, shift, stre,std_nod,std_anc ;
double uncat,maxlimit,minlimit,shifti,stree ;
Sank_spcelltyp ** pt_sank ;
pt_sank = sank_mtx ;

for ( n = intnods  ;  n -- ; ){
       nodo = optlist [n] ;
       if (nodo == nt){   // esto esta mal xq pueden ser mas o menos cuando es recat!!! verrrrr
         inf_limit_cont[ nodo ] = 0 ;
         sup_limit_cont[ nodo ] = nucas   ;}
       for (d = firs[nodo] ; d != - 9  ; d = sis [ d  ] ){
          if (d < nt)
             std_nod = d ;
          else
             std_nod = recons[ qreco ][ d ] ;
          std_anc = recons[ qreco ][ nodo ] ;
          if (pt_sank[std_anc][std_nod].what_best == 0 ){
             inf_limit_cont [ d ] = inf_limit_cont [nodo];
             sup_limit_cont [ d ] = sup_limit_cont [nodo];}
          if (pt_sank[std_anc][std_nod].what_best == 1 ){
             shift=  pt_sank[std_anc][std_nod].best_shft ;
             shift = translator_sh [shift] ;
             shifti = (double) shift ;
             uncat = (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas ; // esto es lo qeu corrije que un cambio de una categ en una tray acortada no es lo mismo q en una cat original
             shifti = shift * uncat ;
             inf_limit_cont [ d ] = inf_limit_cont [nodo] + shifti ;
             sup_limit_cont [ d ] = sup_limit_cont [nodo] + shifti ;}
          if (pt_sank[std_anc][std_nod].what_best == 2 ){
             stre=  pt_sank[std_anc][std_nod].best_str ;
             stre = translator_str [stre] ;
             stree = (double) stre ;
             uncat = (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas ;
             stree = stree * uncat ;
             inf_limit_cont [ d ] = inf_limit_cont [nodo] ;
             sup_limit_cont [ d ] = sup_limit_cont [nodo] + stree ;}
          if (pt_sank[std_anc][std_nod].what_best == 3 ){
             stre=  pt_sank[std_anc][std_nod].best_stri ;
             stre = translator_strinv [stre] ;
             stree = (double) stre ;
             uncat = (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas ;
             stree = stree * uncat ;
             inf_limit_cont [ d ] = inf_limit_cont [nodo] + stree ;
             sup_limit_cont [ d ] = sup_limit_cont [nodo] ; }
           if (pt_sank[std_anc][std_nod].what_best == 4 ){
             stre=  pt_sank[std_anc][std_nod].best_sh_str ;
             shift = translator_sh_str [0][stre] ;
             stre  = translator_sh_str [1][stre] ;
             stree = (double) stre ;
             shifti = (double) shift ;
             uncat = (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas ;
             shifti = shifti * uncat ;
             stree = stree * uncat ;
             inf_limit_cont [ d ] = inf_limit_cont [nodo] + shifti ;
             sup_limit_cont [ d ] = sup_limit_cont [nodo] + stree ; }}}
 round_aln_limits () ;
 minlimit =9000 ; maxlimit = -3000 ;
 for ( n = 0 ;  n < nnods ;n ++ ){
        if (inf_limit_cont [n] < minlimit)
         minlimit = inf_limit_cont[n];
        if (sup_limit_cont [n] > maxlimit)
         maxlimit = sup_limit_cont[n];}

   maxlimit = maxlimit - minlimit ;
  for ( n = 0 ;  n < nnods ;n ++ ){
         inf_limit_cont[n] =  inf_limit_cont[n] - minlimit ;
         sup_limit_cont[n] =  sup_limit_cont[n] - minlimit ;
           }
 return (maxlimit) ;
}

void round_aln_limits () {
    int n , pis, caca ;
  for ( n = 0 ;  n < nnods ;n ++ ){
     if (inf_limit_cont[n] >= 0 )
      inf_limit_cont[n] = inf_limit_cont[n] + 0.5  ;
     else
       inf_limit_cont[n] = inf_limit_cont[n] - 0.5  ;
     sup_limit_cont[n] = sup_limit_cont[n] + 0.5  ;
     caca = (int) inf_limit_cont[n] ;
     pis =  (int) sup_limit_cont[n] ;
     inf_limit_cont[n] = caca ;
     sup_limit_cont[n]=  pis  ; }
  }

void calculate_aln_ages (int iscont) {

  int i, j,conf ;
   Sptyp * pt_sp ;
   Conftyp * pt_conf ;
   pt_sp = sps_list ;
   pt_conf = datamatrix ;

 for (i = 0 ; i < nuspecs ; i ++) {
    pt_sp[i].min_aln_age = 900000 ;
    pt_sp[i].max_aln_age = -99999 ;
    if (iscont)
      {
      for (j = 0 ; j < sps_list [i].num_confs; j++){
       conf = sps_list [i].conflist[j] ;
       pt_conf[conf].age_aln =  inf_limit_cont [i] + ( pt_conf[conf].std_sp_age * ( sup_limit_cont [i] - inf_limit_cont [i] )) ;
       if (pt_conf[conf].age_aln < pt_sp[i].min_aln_age )
         pt_sp[i].min_aln_age = pt_conf[conf].age_aln ;
       if (pt_conf[conf].age_aln > pt_sp[i].max_aln_age )
        pt_sp[i].max_aln_age = pt_conf[conf].age_aln ;} }
   else{
       pt_sp[i].min_aln_age = (double) inf_limit[i] ;
       pt_sp[i].max_aln_age = (double) sup_limit[i] ;}
      }

 }

void calculate_consensus_recat (int totcats,int guichsp ){
int j, l, k, i, son=0;
int nulan ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_sp = sps_list ;
pt_conf = datamatrix ;
nulan = datamatrix[0].nulands ;

for (i = 0 ;  i < totcats   ; i ++)
   align_matrix[guichsp][i].pt[0].x = - 10000001 ;
      for (j= 0 ;  j <  totcats  ; j ++)
        {
         for (l = 0 ; l < nulan ; l++){
         buff_dock[0].pt[l].x = 0;  buff_dock[0].pt[l].y = 0; buff_dock[0].pt[l].z = 0; }
         son = 0 ;
         for (i = 0 ;  i < pt_sp[guichsp].num_confs  ; i ++)
         {
          k = pt_sp[guichsp].conflist[i] ;
          if ( pt_conf [k].which_aln_class == j   ) {
           for (l = 0 ; l < nulan ; l++){
             buff_dock[0].pt[l].x  +=pt_conf[k].pt[l].x ;
             buff_dock[0].pt[l].y  +=pt_conf[k].pt[l].y;
             buff_dock[0].pt[l].z  +=pt_conf[k].pt[l].z;  }
           son ++ ;}
         }
         if ( son > 0 ) {
         for (l = 0 ; l < nulan ; l++){
          align_matrix[guichsp][j].pt[l].x = buff_dock[0].pt[l].x / son ;
          align_matrix[guichsp][j].pt[l].y = buff_dock[0].pt[l].y / son ;
          align_matrix[guichsp][j].pt[l].z = buff_dock[0].pt[l].z / son ;}}
        }
}


void generate_age_covariates (int calin)
{
 avg_aln_age (calin) ;
 do_nd_runtntfile_for_age (calin);
 read_tmp_cont(calin);
}

int read_tmp_cont(catlin){
    int  a=0 ,c,  caca;
    double min ,max ;
    char   bffer [10000] ;
    input_file = fopen ("cont.tmp","rb")    ;
    for (a = 0 ; a < nnods ; a ++ ){
     read_next_line ( bffer) ;
     caca = sscanf ( bffer,"%i%lG%lG}",&c,&min,&max) ;
     min_cont [a] = min ; max_cont [a] = max ; }
  // remove ("cont.tmp");
   return (1);
}


void do_nd_runtntfile_for_age (int calin )   {
int i ;
Sptyp  * pt_sp ;
pt_sp = sps_list ;
sprintf(outputFilename, "ages.tmp");
output_file= fopen(outputFilename, "w");
fprintf(output_file,"\n nstates 32 ; ");
fprintf(output_file,"\n nstates cont ;");
fprintf(output_file,"\nxread\n%i %i",2,nuspecs);
 for ( i= 0 ; i < nuspecs ; i ++)
   {fprintf(output_file,"\n%s_%i ",pt_sp->sps_name,i);
    fprintf(output_file,"%.3f %.3f",pt_sp->minavage,pt_sp->maxavage );
    fprintf(output_file,"");
     pt_sp++ ;
      }

fprintf(output_file,"\n;");
  goto_printree (0) ;

fprintf(output_file,"\ncls ; clb; report- ; sil=all;");
fprintf(output_file,"\nlog cont.tmp; ");
fprintf(output_file,"\n macro=;\n var: arreglo [100] merreglo [100]  ;\n ; ");
fprintf(output_file,"\n iterrecs 0 0 arreglo  killrecs ; endrecs  ; ");
fprintf(output_file,"\n iterrecs 0 1 merreglo  killrecs ; endrecs  ; ");
fprintf(output_file,"\n loop=no 0 nnodes [0] ; ");
fprintf(output_file,"\n sil-all;  quote #no 'arreglo[#no]' 'merreglo[#no]' ;  sil=all; ");
fprintf(output_file,"\n stop; ");
fprintf(output_file,"\n log/; ");
;
fprintf(output_file,"\nzz;");
fclose(output_file) ;

 my_spawn_cont ( ) ;
}


void avg_aln_age (int cats ){
int i, j , cual=0, nusp, nuconf, min = 0, max = 0 ;
double  minavage = 0 , maxavage = 0 ;

Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_sp = sps_list ;
pt_conf = datamatrix ;
nusp = nuspecs ;
nuconf = CONFS ;
for (  i = 0 ;   i < nusp ; i ++ )
   {
      min = 0 ; max = 0 ; minavage = 0 ; maxavage = 0 ;
     for (j = 0 ;  j < pt_sp[i].num_confs  ; j ++)
        {
          cual = pt_sp[ i ].conflist [ j ] ;
          if (  pt_conf[cual].age_aln == inf_limit_cont[i] ){
                 minavage += pt_conf[cual].age ; min++; }
          if (  pt_conf[cual].age_aln == sup_limit_cont[i] ){
                 maxavage += pt_conf[cual].age ; max++ ;}
          }
       pt_sp[i].minavage =  minavage / min ;
       pt_sp[i].maxavage =  maxavage / max ;
        }
}


void  sort_configs_aln_recat (int cats ){
int i, j , cual=0, k, nusp, nuconf ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_sp = sps_list ;
pt_conf = datamatrix ;
nusp = nuspecs ;
nuconf = CONFS ;

for (  i = 0 ;   i < nusp ; i ++ )
 for (j = 0 ;  j < cats  ; j ++)
  yes [i][j] = 0 ;
for (j = 0 ;  j <  nuconf     ; j ++)
  pt_conf [j].which_aln_class = -1 ;

for (  i = 0 ;   i < nusp ; i ++ )
   {
     for (j = 0 ;  j < pt_sp[i].num_confs  ; j ++)
        {
          cual = pt_sp[ i ].conflist [ j ] ;
          if (  pt_conf[cual].age_aln == inf_limit_cont[i] ){ // si es la mas baja es el unico caso que la incluye en la categoria sino el limite pasa a la siguiente.
               for (k = 0 ;  k < cats  ; k ++)
                {
                   if (pt_conf[cual].age_aln == limits_aln_reca[k]){
                     yes[i][k] ++  ;
                     pt_conf[cual].which_aln_class = k ;
                     break ;  }
                }
            continue ;
          }
          for (k = 0 ;  k < cats  ; k ++)
          {
           if ( ( pt_conf[cual].age_aln > limits_aln_reca[k] ) && (pt_conf[cual].age_aln <= limits_aln_reca[k+1] ) ){
             yes[i][k] ++ ;
             pt_conf[cual].which_aln_class = k ;
             break ; }
          }
        }
    }


}


void generate_d_svg (int catl,int iscont) {
int s,sy,x,fy,sx,fx,a,namelen, maxnamelen= -10000, starlin,finlin, dde,linsep,total ;
Sptyp * pt_sp ;
double infdo, supdo,endY ;
char nombre[50] ;
nombre [0] = NULL;
pt_sp = sps_list ;

strcat (nombre,prefix);
strcat (nombre,"_traj.svg");
svg_file= fopen(nombre, "w");

 for (s= 0 ; s < nuspecs; s ++){
     namelen = strlen (pt_sp[s].sps_name) ;
     if ( namelen > maxnamelen )
         maxnamelen = namelen ;}

if (maxnamelen < 5  )   // para q entren los nodos internos
     maxnamelen  = 5 ;
 starlin = (maxnamelen  * 20 )  ;
 finlin = 1300 ; 
 total = finlin - starlin ;
 linsep = total / catl ;
 endY = (50 * nnods) + 50  ;  
 dde = 80 ;

  fprintf(svg_file,"<svg width=\"2001\" height=\"%f\" xmlns=\"http://www.w3.org/2000/svg\" >",endY);
 for (s= 0 ; s < nuspecs; s ++){
     sx = ((pt_sp[s].min_aln_age / catl) * total ) + starlin ;
     fx = ((pt_sp[s].max_aln_age / catl) * total ) + starlin ;
     fprintf(svg_file,"\n<text x= \"0\" y=\"%i\" fill=\"black\"  font-size=\"30\" alignment-baseline=\"middle\"  font-style = \"italic\"   > %s   </text>",dde,pt_sp[s].sps_name );
     fprintf(svg_file,"\n<line x1 = \"%i\" y1 = \"%i\" x2 = \"%i\" y2 = \"%i\" stroke = \"blue\" stroke-width = \"20\"/>",sx,dde,fx,dde);
     dde = dde + 45 ;   } //60 ->50
  for (s= nuspecs ; s < nnods ; s ++){
     if (iscont){
        sx = ((inf_limit_cont[s] / catl) * total ) + starlin ;
        fx = ((sup_limit_cont[s] / catl) * total ) + starlin ;
     fprintf(svg_file,"\n<text x= \"0\" y=\"%i\" fill=\"black\"  font-size=\"30\" alignment-baseline=\"middle\" > Node %i   </text>",dde,nod_p2t[s]  );
     fprintf(svg_file,"\n<line x1 = \"%i\" y1 = \"%i\" x2 = \"%i\" y2 = \"%i\" stroke = \"blue\" stroke-width = \"20\"/>",sx,dde,fx,dde);
     dde = dde + 45 ; }//60 ->50
     else
     {
        infdo = (double)  inf_limit[s]  ;
        supdo = (double)  sup_limit[s]  ;
        sx = ((infdo / catl) * total ) + starlin ;
        fx = ((supdo / catl) * total ) + starlin ;
     fprintf(svg_file,"\n<text x= \"0\" y=\"%i\" fill=\"black\"  font-size=\"30\" alignment-baseline=\"middle\" > Node %i   </text>",dde,nod_p2t[s] );
     fprintf(svg_file,"\n<line x1 = \"%i\" y1 = \"%i\" x2 = \"%i\" y2 = \"%i\" stroke = \"blue\" stroke-width = \"20\"/>",sx,dde,fx,dde);
     dde = dde + 45 ; } //60 ->50
       }
x = starlin ;
sy = 20 ;
fy = 70 + 45 * ((2 * nuspecs) -1);
for (a = 0 ; a < catl ; a ++ ){
     fprintf(svg_file,"\n<line x1 = \"%i\" y1 = \"%i\" x2 = \"%i\" y2 = \"%i\" stroke-dasharray=\"15,5\" stroke = \"black\" stroke-width = \"2\"/>",x,sy,x,fy);
     fprintf(svg_file,"\n<text x= \"%i\" y = \"%i\" font-size=\"30\" >  %i </text> ", x + linsep/2,sy,a);
     x = x + linsep ;
       }
 fprintf(svg_file,"\n<line x1 = \"%i\" y1 = \"%i\" x2 = \"%i\" y2 = \"%i\" stroke-dasharray=\"15,5\" stroke = \"black\" stroke-width = \"3\"/>",x,sy,x,fy);
fprintf(svg_file,"\n</svg>"); 

fclose (svg_file) ;

}

int procargs ( int nargs , char ** arg )
{
    int i ;
    char * cp ;
    int  case_d=0,  case_c =0, case_t = 0, case_i = 0 ;
    char age [5] ;
    //Globals:
    doskfile= 0; doasisfiles= 0; do_classif= 0 ; do_covfile=0 ; do_resample = 0 ;  maxstages= 0;pen_fac = 1 ; pen_ext = 1 ,outusrname ;
    dosvg = 1 ;  dospeclist = 0 ; do_deca= 0 ;
    if ( nargs == 1 ) {
        giveme_help (  ) ;
        return( 0 ) ; }
    for ( i = 1 ; i < nargs ; ++ i ) {
        cp = arg [ i ] ;
        if ( * cp  != '-' ) {
            fprintf ( stderr , "\nWrong argument: %s\n" , arg [ i ] ) ;
            exit ( 0 ) ; }
        switch ( * ++ cp ) {
            case 'i':  cp = arg [++i] ; strcpy (inputFilename,cp)  ; case_i = 1 ;
               if (( input_file = fopen (inputFilename,"rb") )== NULL){
                   printf ("Error. \" Input file \"%s\" not found",inputFilename ) ;
                   return (0); }
               break ;
            case 'r':   do_resample = 1 ;
                   cp = arg [++i] ;
                   replications = atoi ( cp ) ;   break ; /*resampling*/ /* falta testeo q sean menos de 1000  o alocar resampling despues de leer esto*/
            case 't':  cp = arg [++i] ; strcpy (treeFilename,cp)  ; case_t = 1   ; break ;
            case 'k': doskfile = 1 ;       break ;   /* generate sankoff matrix with costs */
            case 'o': doasisfiles = 1 ;  break ;       /* infer ancestral ontogenetic trajectories in teh original frame of comparsion */
         //   case 'j': do_covfile = 1 ;      break ;       /*generate covariates and  for morphoJ*/
            case 'y': do_deca = 1 ;      break ;       /*give decay support values*/
          //  case 's': do_classif = 1 ; break ;     /*generate classifiers for morphoJ*/
            case 'x': pen_ext = 0 ; break ;     /* assign a penalty independent of the number of stages implied in the change */
            case 'p':  cp = arg [++i] ;
                   pen_fac = atoi ( cp ) ; break ;
            case 'v': dosvg =  0;   break ; /*do not generate an svg file with implied aligment of ontogenetic trajectories */
            case 'l':  dospeclist = 1 ; break ; /* Make a txt file listing specimens included in each stage for all the species */
            case 'u':  outusrname= 1 ;
                       cp=arg[++i];
                       if (i == nargs || * cp == '-' ){
                          printf("\nError while reading arguments. No prefix for output files  (-u myprefix) ");
                          return (0);}
                        strcpy(prefix,cp);
                        break; //define a prefix for output files
            case 'a': cp = arg [++i] ;
               if (i == nargs || * cp == '-' ){
                 printf("\nError while reading arguments. Indicate if age is given as continuous variable (-a cont) or as predefined stages (-a pre)");
                          return (0);}
                strcpy(age,cp);
                if (!strcmp (age,"pre")){
                    timeas = 0 ; case_d = 1 ;        
                    cp = arg [++i] ;
                    if (i == nargs || * cp == '-' ){
                      printf("\nError while reading arguments. Indicate number of a priori defined stages ");
                      return (0); }
                NUCATEG = atoi ( cp ) ;
                break;  }
                else{
                   if (!strcmp (age,"cont")){
                      timeas = 1 ; case_c = 1 ;       
                      cp = arg [++i] ;
                      if  (i == nargs )
                        NUCATEG = -1 ;
                      else
                       if ( * cp  == '-'){
                         NUCATEG = -1 ;
                         i-- ;
                         cp-- ; }
                       else
                        NUCATEG = atoi ( cp ) ;
                       break ;}
                   else{
                    printf("\nError while reading arguments. Wrong string  \"%s\". Indicate if age is given as continuous variable (cont) or as predefined stages (pre)",age);
                          return (0);} }
           }

    }
    if (!case_i){
        printf("\nError while reading arguments. Indicate input file (-i \"myinputfile.tps\") ");
        return (0); }
    if (!case_t){
        printf("\nError while reading arguments. Indicate tree file (-t \"mytrefile.tre\")");
        return (0); }
    if (!case_d && !case_c){
       printf("\nError while reading arguments. Indicate whether individuals are sorted ");
      printf("\nin aprori defined stages (-d), or age is given as a continuos variable (-c)");
      fflush(stdout);
      return (0); }

    return (1);
}

void giveme_help (  ) {


printf("\n  ------------------------------------------------- ");
printf("\n |                * SPASOS v. alpha *              |");
printf("\n |     Software for the Phylogenetic Analysis      |");
printf("\n |              of Shape Ontogenies                |");
printf("\n  ------------------------------------------------- ");
printf("\n\n* Mandatory arguments"); 
printf("\n\n -i \"myinputfile.tps\"  Input tps file ") ;
printf("\n\n -t \"mytreefile.tre\"   Input tree file ");
printf("\n\n -a cont / pre N. Indicate if age is given as a continuous variable (cont) or as predefined stages (pre)");
printf("\n       If age is given as predefined stages, the number of stages (N) should be indicated after the "); 
printf("\n       string \"pre\". In the case of age given as continuous variable, SPASOS divides the ontogenetic");  
printf("\n       trajectories in the maximum number of stages without missing data. Optionally, the user can indicate");
printf("\n       the number of stages after the string \"cont\""); 
printf("\n\n* Optional arguments"); 
printf("\n\n -l     Make a txt file listing specimens included in each stage for all the species ");
printf("\n\n -o     Infer ancestral ontogenetic trajectories in the original frame of comparison  ");
printf("\n          i.e. force no change in developmental timing in all branches");
printf("\n\n -p   N Define a penalty factor ( 1 lower, 5 highest). Default 1 ");
printf("\n\n -r   N Perform resampling (N replicates)");
printf("\n\n -u  \"myprefix\" Give a prefix for output files");
printf("\n\n -v     Do not generate an svg file with implied alignment of ontogenetic trajectories ");
printf("\n\n -x     Assign a penalty equal for all changes in developmental timing irrespective of the number of stages implied ");
printf("\n        in the change ");
printf("\n\n -y     Calculate decay support values");
printf("\n        is no longer retrieved when the analysis is repeated considering a penalty 10%% higher ");  
//printf("\n\n -j     Generate classifiers for morphoJ ") ;
//printf("\n\n -k  Generate a file with the sankoff matrix in TNT format calculated in PASOS ");
}


int process_datafile(){
int yeso,h ;
yeso = define_dimensions ();
if (!yeso){
  printf ("Problems while reading tps file") ;
  fflush(stdout);

  return(0);}
fclose (input_file) ;
input_file = fopen (inputFilename,"rb") ;
if (DIMS < 2 ){
   printf ("Error, argument 3 (dimensions) can only take two values (2-3)") ;
   fflush(stdout);

   return(0); }
 datamatrix = (Conftyp *) malloc ( CONFS * sizeof(Conftyp) ) ;
 for (h=0; h<CONFS ; h++ ){
   datamatrix[h].pt =  (Punktyp *) malloc ( LANDS *   sizeof(Punktyp)) ;
   datamatrix[h].sps_name[0]='\0' ; }
if (!read_data ()){
     return(0); }
if (!timeas )
 if (!check_cats())   
   return(0) ;     
return (1) ;
}


int check_cats ( ) {
int i, mincat=100000, maxcat = -10000 ;
Conftyp * pt_conf ;
pt_conf = datamatrix ;

  for (i = 0 ; i < CONFS ; i ++){
    if (pt_conf->age > maxcat )
       maxcat = pt_conf->age ;
    if (pt_conf->age < mincat )   
        mincat = pt_conf->age ;
        pt_conf++; }
 if (mincat > 0 ){
   printf("Error with discrete stages. First stage should be 0, (%i in datafile)",mincat);
   return (0);}
 if ( ( maxcat +1  ) != NUCATEG) {
   printf("Error. Number of stages in datafile (%i) differs from that indicated in the command line (%i)",(maxcat+1),NUCATEG);
   return (0); }
 return (1); 
}


int alloc_matrices(){
  alloc_consense_matrix (STATES,NUCATEG,LANDS) ;
  alloc_optimus_matrix  (nnods,CATALINS,LANDS) ;
  alloc_sank_mtx ( ) ;
  alloc_downcosts ( ) ;
  alloc_upcosts ( );
  alloc_final_states ()  ;
  alloc_ispoli () ;
  alloc_branch_labels ();
  buff_dock = (Conftyp *) malloc ( 1 * sizeof(Conftyp) ) ;
  buff_dock[0].pt =  (Punktyp *) malloc ( LANDS *   sizeof(Punktyp)) ;
 }


void dealloc_matrices (){
 dealloc_branch_labels () ;
 dealloc_datamatrix ( nuconfs ) ;
 // dealloc_consense_matrix ( nuspecs, NUCATEG, LANDS )  ;
 dealloc_sank_mtx () ;
 dealloc_downcosts () ;
 dealloc_final_states () ;
 dealloc_recons () ;
}

void show_indiv_list () {
 int a , j,cual  ;
 Sptyp * pt_sp ;
 char nombre [50];
 Conftyp * pt_conf ;
 pt_conf = datamatrix ;
 pt_sp = sps_list ;
nombre[0] = NULL ;
 strcat(nombre,prefix);
 strcat(nombre,"_specimens.out");

sank_file= fopen(nombre, "w");
fprintf(sank_file,"\nSpecies ,Specimen ,Stage");
for (a = 0 ; a < nt ;  a++){
  for (j = 0 ;  j < pt_sp[a].num_confs  ; j ++){
     cual = pt_sp[a].conflist[j];
     fprintf(sank_file, "\n%s  , %i ,  %i",pt_sp[a].sps_name,cual,pt_conf[cual].which_class);
  }}
  fclose (sank_file);
}


void do_output_prefix() {
int start,largo ;
char *charp ;
if (!outusrname){
 start = &inputFilename ;
 charp =strchr(inputFilename,'.');
 largo = charp - start ;
 strcpy(prefix,inputFilename) ;
 prefix [largo] = '\0';}
}

void triangle_ineq (){
int wrong = 0;

  if (!test_triangle_inequality ())
    return ;
  else{
   wrong = 1;
   while (wrong ==1){
     wrong =correct_triangle_inequality () ;}
    printf("\nWarning: triangle inequality violated. Fixed");
     }
}


int do_decay (){
int n, yeso, opt_asis,a,b ,vta, falta;
double newscore, pace, cto, pen_orig ;

fill_consense_matrix ( nuspecs, NUCATEG, LANDS) ;

for (n=0 ; n < nnods ; n++){
  if (transformations[n] == 0 )
    support [n ]  = 0;
 else
    support [ n ] = -1  ;
}
  conf_x_categ (nuspecs,NUCATEG ) ;

 pace = 0.1 ;

vta = 0 ;
pen_orig = penalty ;

while (1){
 penalty = pen_orig * ( 1 + (pace * vta) )  ;
 dde_cns_mtx =nuspecs ;
 if (extended)
    build_extended_states(nuspecs, NUCATEG) ;
  max_modif = calculate_max_modif (NUCATEG,nuspecs) ;
  for( a = 0 ; a < STATES  ;a ++ )
    for ( b = 0 ; b < STATES  ;b ++ ){
      if (a == b ) continue ;
         make_as_is (a,b,NUCATEG,STATES) ;}
   fill_sankoff_costs(nuspecs,NUCATEG) ;
  put_best_score (NUCATEG) ;
  triangle_ineq () ;
  yeso=0  ;  opt_asis = 0;
  sank_downpass () ;
  sank_uppass () ;
  newscore= fill_reconstructions_new (nt) ;
  cto = vta * pace ;
  map_support (0,cto) ; // aca tengo que ver como envio la info. Tengo qeu decidir q info guardo*/
    falta = 0 ;
   for (n=0 ; n < nnods ; n++) {
     if (n == nt )
       continue ;
       if (support[n] == -1 ){
        falta ++ ;
         break; }
     }
     if (falta == 0 )
      break ;
vta ++ ;
 }
return (1) ;
}


void map_support(int qreco, double value){
int n,  std_anc,std_nod ;
Sank_spcelltyp ** pt_sank ;
pt_sank = sank_mtx ;
fflush(stdout);
 for (n =  0 ; n < nnods ; n++ )
 {
   if (n == nt)
      continue ;
   std_anc = recons[ qreco ][ ances [n] ];
   if (bak_all_trans[n][5] > 1 && (ances [n ] != nt ) ){
     support [n] = 0 ;
     continue ; }
   if ( n < nt )
      std_nod = n  ;
   else
     std_nod = recons[ qreco ][ n ];
  if ( (pt_sank[std_anc][std_nod].what_best == transformations [n])|| (support[n] != -1) || (transformations [n] == 0   ))
    continue ;
  else
    if ( pt_sank[std_anc][std_nod].what_best == 0 && (support[n] == -1) ){
       support [n] = value ;}
   }

}//map_support


void do_supports(){
  char nombre [300] ;
 if ( do_resample ){
   printf("\r                                  ");
   printf("\nPerforming resampling...");
   resample (nuspecs, NUCATEG, extended) ;}
 if (do_deca){
    do_decay() ;
   printf("\r                                  ");    
   printf("\nCalculating decay values...");
    }
fclose (output_file);
strcpy (nombre,prefix);
strcat (nombre,"_tags.tre") ;
strcat (nombre,"\0");
caca_file = fopen(nombre,"w+");
//fprintf (caca_file,"caca");
goto_printree_support();
close (caca_file);
strcpy (fintreFilename, nombre);
printf("\r                                  ");
}

int my_spawn_tree_svg( )
{
    char jstr[(360*2)+256] ;
    char qqqstr[60]    ;
    char name [300 ] ;
    STARTUPINFO startinfo;
    PROCESS_INFORMATION pinfo;
    DWORD how;
    how = 0;
    output_file = fopen ("svg.tmp","w");
    strcpy (name,prefix);
    strcat (name,"_tree.svg");
    fprintf(output_file,"ttag &%s bheight 40 ; zz ;",name);
    fclose (output_file);
    strcpy(qqqstr,"tnt ") ; //tiene que ir el nombre del archivo y el del script separado por ;
    strcat (qqqstr,finalFilename) ;
    strcat (qqqstr," ") ;
    strcat (qqqstr,fintreFilename) ;
    strcat (qqqstr," svg.tmp") ;
    startinfo.cb = sizeof(STARTUPINFO);
    startinfo.lpReserved = NULL;
    startinfo.lpDesktop = NULL;
    wsprintf(jstr,"RUNNING TNT");
    startinfo.lpTitle = jstr;
    startinfo.dwFlags = STARTF_USEPOSITION | STARTF_USESIZE ;
    startinfo.dwX = 50 ;
    startinfo.dwXSize = 700 ;
    startinfo.dwY = 100 ;
    startinfo.dwYSize = 250 ;
    startinfo.cbReserved2 = NULL;
    startinfo.wShowWindow = SW_SHOW;
       if(CreateProcess(NULL, qqqstr, NULL, NULL, FALSE ,
            HIGH_PRIORITY_CLASS | 0, NULL, NULL, &startinfo, &pinfo))
        WaitForSingleObject(pinfo.hProcess,INFINITE);
            else {
                MessageBox(hwnd,"TNT could not be started!","TNT executable should be is in the same folder than SPASOS",MB_OK | MB_ICONERROR );
                return(255);
            }
        GetExitCodeProcess(pinfo.hProcess, &how);
remove ("svg.tmp"); 
  
        return( how );
}
