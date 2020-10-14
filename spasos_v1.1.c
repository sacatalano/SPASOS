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

// CALCULAR EL COSTO DE MANERA QUE SE beneficien los sh_str. Por otra parte hacer solo shift y stre_sh asi puedo hacer un heuristico en cada funcion. Ver penalidad que ahora la baje.
// INFORMAR NO COMO SH STRE SINO COMO CAMBIOS AL PPIO Y AL FINAL.
 int flag = 0 ;


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
FILE * output_file , *tmp_file , *trans_tmp_file, * sank_file, * svg_file , * caca_file, *dispar_file, *outputfile  ;
char outputFilename[300]  ;
char inputFilename[300] ;
char treeFilename[300] ;
char finalFilename [300] ;
char fintreFilename[300] ;
char fintreFilename_2[300] ;
char otherFilename[300]  ;
char asisFilename [300] ;
char tntexe[ 2000 ] ;
extern char ** sps_names ;

void check_monotonicity(int ) ;

double sum_wts_fxd_antes      (int sps,int pivot,int winsizfxd, double *  wts_pt, double * prod_pt, int ) ;
double sum_wts_fxd_nuevo(int sps,int pivot,int nupts, int *  wts_pt, double * prod_pt) ;

typedef struct { double x, y, z ; } Punktyp ;
typedef struct  {
     Punktyp *pt   ;
     double age ;
     double std_sp_age ;
     double age_aln ;
     char sps_name [ 300 ] ;
     int sp_number ;
     int confnumber ;
     char ind_number [300];
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
     int confminage;
     int confmaxage;
     char * sps_name ;
     int sp_number ;
     int conflist [MAXINDXSP] ; } Sptyp ;

typedef struct {
     double score_shft [ MAXCOMP] ;
     double score_str [ MAXCOMP ] ;
     double score_str_inv [ MAXCOMP ] ;
     double score_asis ;
     double score_sh_str [ MAXCOMP ] ;
     int best_stri ;
     int best_shft ;
     int best_str ;
     int best_sh_str ;
     int what_best ; // 0 = asis, 1= shift, 2 str; 3 stri; 4 double_str ;
     double best_overall  ; } Sank_spcelltyp ;

typedef struct {
     Punktyp * pt ; int numrecs ;
      } Landcelltyp ;

int interpolate_cont(int,int );
void give_consense(int );
extern int goto_read_tree (int) ;
extern int goto_printree (int) ;
extern int goto_printree_support (int) ;
void improve_map_changes (int );
int intnods,  nt ;
extern int nnods ;
extern int firs [ MAXNODES ], sis  [ MAXNODES ],optlist[ MAXNODES ], ances [MAXNODES] ;

double min_cont [MAXNODES],max_cont [MAXNODES] ;

int excluido [MAXSPECIES][MAXINDXSP] ;

double  trans_corr [2][MAXNODES], catlin_reco [MAXRANDOM] ;
int minageconf, maxageconf;
int WAT_CHG, orig_confs;
double  pen_orig ;

int FXDPTS =3; // FXDPTS = 10
int excl[MAXSPECIES][MAXINDXSP];
double wts [MAXSPECIES][CAT_INTER]  ;
double sum_wts(int,int,int);
double sum_wts_fxd(int ,int ,int,  int *, double *  );
int replications = 100 ;
int nuspecs, nod_t2p [MAXNODES],nod_p2t [MAXNODES], transformations [MAXNODES], transform_rnd [MAXNODES][MAXRANDOM],guich_rnd [MAXNODES * 2 ][MAXRANDOM],guich_map [ MAXNODES * 2 ]  ; // aca hay que alocar dinamicamente transform
double inf_limit_resa[MAXRANDOM][MAXNODES],sup_limit_resa[MAXRANDOM][MAXNODES],sup_limit_back[MAXNODES],inf_limit_back[MAXNODES] ;
int all_trans [MAXNODES][6],bak_all_trans [MAXNODES][6],bak_transf[MAXNODES],easy_trans[ MAXNODES ][ 2 ],bak_easy_trans[ MAXNODES ][ 2 ], easy_trans_rnd[MAXRANDOM][ MAXNODES ][ 2 ],   chg[ MAXNODES ][2] ; // last cel= ambig/no ambig

int ctos_ahi [2][CATALINS],error[MAXSPECIES][2][2] ;
double disparity  [CATALINS];
double dispar_lim [CATALINS] ;
int vanss [ CATALINS];

double penalty  ;
int penalize = 1, do_resample, do_deca ;
int traffo [1000], pen_fac =1, gap_fac = 5  ;
char ** branch_labels, ** cats_labels, ** transf_label,**color_labels,** back_labels ;
int trans_freq [MAXNODES][2], nuconf_sp_clas [MAXSPECIES][MAXCATEGS], timeas=1,doshift, dostre, doinvstre, doshstre, doasis= 1, opt_asis, cost_ends = 0, pen_ext, istps=0, color_tree =  1, blue_red = 1 , old_mj = 0  ;
double trans_relf [MAXNODES][2] ;
char altype [50], bltype [50], prefix[50] ;
int desc [ MAXNODES ], dde = 0 ;
double brnch_scor [MAXNODES], horiz[MAXNODES],vert[MAXNODES],chg_asis[MAXNODES],comp_horiz[MAXNODES],comp_vert[MAXNODES] ;

int trece= 0 , dos= 0 , OUTGRP ;
double core,  scor_AS_TNT,scor_H_TNT, scor_H_FS, scor_AS_reco,scor_AS_FS ;

int ** final_states=NULL, ** recons=NULL,  totrecs, ruta,  * ispoli, * opt_recons, numrecos, where [MAXNODES] ;
double mincost(int  , int    ) ;
double land_diff      (Punktyp * , Punktyp * ) ;
double pair_conf_dist (Punktyp * , Punktyp * ) ;
double calculate_disparity ( int) ;
double truncate (double ) ;
int maxdists [MAXSPECIES];
void generate_output_file (int,char*) ;
int borrar_espacios(char *  ) ;
void put_cats_inlabels (int cats) ;
void define_final_states ( int ) ;
int my_spawn_hetero () ;
int my_spawn_asis () ;
void fill_alignment_w_consense_doall(int guichsp,int nucats, int doall)  ;
void alloc_consense_matrix (int,int,int) ;
void alloc_interp_trajec ( ) ;
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
void define_limit_stretch (  int , int , int,int  ) ;
int sorting_confs_in_cats_stretch ( int , int , int, int , int,int,int  ) ;
int fill_w_consense_stretch (int ,int, int,int,int) ;
void fill_doc1_w_consense_asis ( int, int ) ;
void giveme_help (  ) ;
void round_aln_limits (int ) ;
void generate_aln_file(int ,int  );
int r_stretchs (int);
void fill_consense_matrix_resample(int,int,int);
int define_d_pairings( int, int, int);
void generate_tps_shift (int) ;
int accept_sh_str(int,int,int);
void complete_all_trans ();
void generate_species_classif_recat (int );
void conf_x_categ (int,int);
void cpy_one (int,int) ;
int sample_datamatrix ();


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
int read_data ();
void generate_alignment_asis (int,int ) ;
int generate_alignment_recat ( int, int, int ) ;
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
double define_d_pairings_recat (int qreco,int nucas,int resa) ;
double make_d_shifts_penalty (int ,int ) ;
double make_d_shifts_tripet (int,int,int,int,int);
double make_d_shifts_tripet_both (int,int,int,int,int);
double make_d_shifts_tripet_int(int,int,int,int,int);
double score_by_branch (int asis) ;
double limits [MAXNODES] [MAXCATEGS], limits_str [MAXNODES],limits_aln [MAXNODES] [MAXCATEGS],limits_aln_reca [MAXNODES],  **downcosts=NULL, *upcosts=NULL, mincosto  [MAXNODES], refer_score, max_modif ;
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
void generate_d_svg (int  ,int,int,int  ) ;
void  sort_configs_aln_recat (int  );
int read_tmp_cont(int);
void generate_tmp_file_hetero () ;
int  read_tmp_data_recat(int ) ;
void define_limit_db_stretch(int,int,int,int) ;

int translator_sh [100000], translator_str [100000],translator_strinv [100000], translator_sh_str[2][100000],translator_str_sh[2][100000], jumany_sh, jumany_str, transo ;
int mask_aln[MAXNODES][MAXCATEGS];
int dde_cns_mtx ,mobes [5] ;

void build_extended_states(int nuspecs, int nucateg);
int calculate_nustates(int);
int extended = 0, ctos_recu ;

void alloc_branch_labels ();
void dealloc_branch_labels () ;
double calculate_max_modif (int,int);

void dealloc_datamatrix (int) ;
void fill_consense_matrix (int, int, int) ;
Conftyp * dock1, * dock2, * buff_dock, * consense_dispar ;
Conftyp ** buff_traj, * bes_traj ;
double fermat_scale= 0.001, esco , scor_improved;
Conftyp * datamatrix, **align_matrix, * back_mtx ;
Sank_spcelltyp ** sank_mtx ;
Conftyp ** consense_matrix, ** optimus_matrix, **interp_trajec, ** bak_consense_matrix  ;
Sptyp * sps_list , * bak_sps_list;
Punktyp * pt1, * pt2 ;
int ** firs_conf ;
int **sis_conf ;

int b,skip_optim=0, contlin = 0, dimens = 2, yes [ MAXSPECIES ][ CAT_INTER ] , van [MAXSPECIES][CAT_INTER] , chsn_obs [ MAXSPECIES ][ CAT_INTER ]  ;
int  yes_str [ 100 ], nuconfs,nuland,NUCATEG= 0,nuspecs,dime, inf_limit [MAXNODES], sup_limit [MAXNODES], position [MAXCATEGS], stretch_value [ 100 ] ;
int doskfile= 0, doasisfiles= 0, do_classif= 0 , do_covfile=0 ,  maxstages= 0,dosvg= 1, dospeclist= 0, outusrname=0; dodisparity = 0,dointerp = 1, dogapping=0, doperc= 0, use_observed= 1,dowindmax=0 ;
int givages = 0, cat_alin, dispar_var ;
double inf_limit_cont [MAXNODES], sup_limit_cont [MAXNODES]  ;
int CONFS, DIMS, LANDS, STATES, windsize ;
char archivo [ 50 ];
double support [MAXNODES][2];





int main (int argc, char * argv[])
{
 int i= 0 , h ,  a= 0 , b,  tadde, dde,  doall,catal, max, dif, val, stra  ;
 int  yeso, confi, son , s ;
 double doble ;
 char  numero [5], nombre [40] ;
// srand(time(NULL));

numero [0] = NULL ;

if (!procargs ( argc , argv ) )
 return (0) ;
if (process_datafile() == 0)
  return (0);
if (!goto_read_tree (nuspecs)){
    return ( 0 ) ; }

if (timeas || dointerp)
  doall = 1 ;
 else
  doall = 0;
//cost_ends =1;
if (doall){
    doshift = 0 ; //1
    dostre = 1 ;
    doinvstre = 1 ;//1
    doshstre = 1 ;}//1
 else{
      doshift = 0 ;
     dostre = 1 ;
    doinvstre = 0 ;
    doshstre = 0 ;}

 input_file = fopen (inputFilename,"rb");

   ;
 a = 0 ;
  if (nuspecs != nt ){
   printf("\n tps and tree files have different number of species: %i vs. %i respectively ",nuspecs,nt);
   printf("\nSpecies names in tree file");
   for (i = 0 ; i < nt ; i++ )
      printf("\n%s",sps_names[i]) ;
   printf("\nSpecies names in tps file");
   for (i = 0 ; i < nuspecs ; i++ )
      printf("\n%s",sps_list[i].sps_name);
      return(0);  }

 if (extended )
    STATES = calculate_nustates(nuspecs);
 else
    STATES = nuspecs ;

 minmax_age_sp (nuspecs) ;
 bak_minmaxage(); // guardo en bak_sps_list las min y maxage con la numeracion original de las configs
 define_relative_ages ( nuspecs ) ;

 if ( dointerp ){
   alloc_intlists() ;
   alloc_interp_trajec ( ) ;
   fill_bakmtx(); //backapea too sps_list[s].num_conf
   interpolate_cont( CONFS , 0 ) ; // aqui modifico timeas = 1 y desde este punto son todos
   orig_confs = CONFS ;
   NUCATEG = CAT_INTER_AVG ;
   son = 0 ;
   if (use_observed){
    for (s= 0 ; s < nuspecs; s++)
       son +=sps_list[s].num_confs; // sps_list fue actualizado en fill_dmatrix_winterp
    CONFS = son ;  }
   else
     CONFS =  CAT_INTER * nuspecs; }
printf("\nPre-processing...");
yeso = 0; max = 0 ;
 if (timeas){
      if (NUCATEG > 0 ){
       define_limits ( NUCATEG , nuspecs ) ;
       yeso= sorting_confs_in_cats ( NUCATEG , nuspecs , CONFS,1 ) ;
       if (!yeso){
       return (0);}
       }
      else{
       for (i= 4 ; i < 50 ; i++) {//31
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


if (!dointerp)
give_original(2);


fflush(stdout) ;

if (dogapping){
 //do_gapped_trajects_cont() ;
 do_gapped_trajects_fragm ();
 /*do_gapped_trajects_categs() ;*/
  }
if (!dointerp)
 give_gapped(2);

do_output_prefix() ;
print_settings ( ) ;
if (dospeclist)
   show_indiv_list ();
alloc_matrices ();
tadde = NUCATEG   ;
generate_dock (NUCATEG);
dde = 0 ;
fill_consense_matrix ( nuspecs, NUCATEG, LANDS) ;
fill_bak_consense_matrix ( nuspecs, NUCATEG, LANDS) ;
//check_monotonicity(NUCATEG);


dde_cns_mtx =nuspecs ; //para extended

if (dointerp && dogapping)
 give_consense(2);

if (extended)
  build_extended_states(nuspecs, NUCATEG) ;

//max_modif = calculate_max_modif (NUCATEG,nuspecs) ;
alloc_buff_traj(NUCATEG) ;
transo = 0 ;
for( a = 0 ; a < STATES  ;a ++ )
   for ( b = 0 ; b < STATES  ;b ++ ){
      if (a == b ) continue ;
         make_as_is (a,b,NUCATEG,STATES) ;}

 if (penalize){
  calculate_penalty (nuspecs,NUCATEG ) ;
  pen_orig = penalty ; }
 else
  { penalty = 0 ;  pen_fac= 0 ;}
if (pen_fac !=10000)
 printf("\nPenalty:%f",penalty);

/*if (dowindmax)
 printf("\nMaximum window");
else
  printf("\nMinimum window");

if (cost_ends)
 printf("\nCost Ends");
else
 printf("\n NO Cost Ends");

printf("\nFxdpts:%i",FXDPTS);*/

fflush(stdout) ;



printf("\nRunning the analysis...");

fill_sankoff_costs(nuspecs,NUCATEG) ;
put_best_score (NUCATEG) ;
triangle_ineq ();



/*if (1){//if (doskfile)
    test_sank_mtx();
 generate_sank_mtx();  }*/
jusout ();


catal  = optimize_tree_hetero (doall) ;

bakap_all_trans () ;
check_ambiguity() ;
//make_a_list() ;


do_supports () ;
bak_branch_labels();
if (!color_tree){
make_ttags (0) ; //	para dar colores
modify_labels(0) ;
fclose (output_file);
strcpy (nombre,prefix);
strcat (nombre,"_tags_onset.tre") ;
strcat (nombre,"\0");
caca_file = fopen(nombre,"w+");
//fprintf (caca_file,"caca");
goto_printree_support(0);
fclose (caca_file);
strcpy (fintreFilename, nombre);
my_spawn_tree_svg(0) ;
remove (nombre);
restor_branch_labels();}

//ESTOY ACA GENERANDO DOS SVGS Y DOS .TRE PARA COLOREARLOS EN AMBOS //
make_ttags (1) ;
modify_labels(1) ;
strcpy (nombre,prefix);
strcat (nombre,"_tags_offset.tre") ;
strcat (nombre,"\0");
caca_file = fopen(nombre,"w+");
//fprintf (caca_file,"caca");
goto_printree_support(1);
fclose (caca_file);
strcpy (fintreFilename_2, nombre);
printf("\r                                  ");
my_spawn_tree_svg(1) ;
remove(nombre);

fflush(stdout);
freeing () ;
fflush(stdout) ;
printf("\r                                    ");
printf("\nDONE!!!");
return(0) ;
} //main



bak_branch_labels(){
int n ;
 for (n = 0  ;n < nnods  ;n++)
  strcpy (back_labels[n],branch_labels[n]);
}


modify_labels (int limit){
int i,n,len ;
char * pt_char, * pt_star ;
for (n = 0  ;n < nnods  ;n++){
  len = strlen(branch_labels[n]) ;
  pt_char = strchr(branch_labels[n],'|');
  if (pt_char == NULL)
    continue ;
  if ( limit == 0 )
	  strcpy(pt_char,"\0") ;
  else 	  {
    pt_char++ ;
    strcpy(branch_labels[n],pt_char) ; }
 if (branch_labels[n][0] == 48 )
    strcpy(branch_labels[n],"\0"); }
}
restor_branch_labels(){
int n ;
 for (n = 0  ;n < nnods  ;n++)
  strcpy (branch_labels[n],back_labels[n]);
}




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
int ctos, u,a,v,  i, ind,  j ;
char * pt_orig, * pt_l,stri[100] ;
   pt_orig = pt_chr ;
  if (isdigit (* pt_chr)  ){
       printf ("\nError! Specimen %i has more than %i lands (approx. line %i)",guichconf,LANDS,contlin);
   return (-1); }
   for(i = 0; i<100; i++)
     stri[i] = tolower(pt_chr[i]);
  //if  ( ( strstr ( pt_chr,"LM=") != NULL ) || ( strstr ( pt_chr,"AGE=")   != NULL  ) || ( strstr ( pt_chr,"LM3=") != NULL ) )  {
  if  ( ( strstr ( stri,"lm=") != NULL ) || ( strstr ( stri,"age=")   != NULL  ) || ( strstr ( stri,"lm3=") != NULL ) )  {
        printf ("\nError! Specimen %i lacks species information(approx. line %i)",guichconf,contlin);
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
          printf("\nError! No species name at specimen %i, approx. line %i ",guichconf,contlin);
            return (-1);}
        if ( strchr ( pt_chr, '/')  == NULL) {
           strcpy(datamatrix[guichconf].sps_name,pt_chr)  ;
           pt_l = datamatrix[guichconf].sps_name ;
           for (a = 0 ; a < 300 ; a ++ ) { //para borrar espacios al final
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
          v = 0 ;
          pt_chr++ ;
          for ( j = (pt_chr - pt_orig) ; j < largo ; j++)
           if (! (* pt_chr == EOF) || (* pt_chr == '\n')){
            datamatrix[guichconf].ind_number[v] = * pt_chr;
            pt_chr ++ ;
            v++ ;  }
             //datamatrix[guichconf].ind_number = atoi (pt_chr) ;}
       return ( 1 ); }
       }
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
   if (  (strstr ( stri,"lm=") != NULL) || (strstr ( stri,"lm3=") != NULL)  )  {  //FLAG
        printf ("\nError! Specimen %i lacks age information(approx. line %i)",guichconf,contlin);
        return (-1); }
   else
    if ( (strstr ( stri,"age=") )  != NULL ){
         pt_chr+= 4 ;
         ctos = borrar_espacios(pt_chr) ;
         pt_chr += ctos ;
         if ((pt_chr - pt_orig  ) == largo) {
          printf("\nError! No age for specimen %i, approx. line %i  ",guichconf,contlin);
            return (-1);}
         if (!isdigit(pt_chr[0])){
           printf ("\nError while reading the Age of specimen %i. Char. \"%c\"  found (approx. line %i)",guichconf,pt_chr[0], contlin);
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

int count_species (int confs ) {
 int i, j,  espec, dde, guere= 0 , diff;
 espec = 1 ;

sps_list=       (Sptyp * ) malloc (MAXINDXSP * (sizeof (Sptyp))) ;
for (i= 0; i< MAXINDXSP; i ++)
       sps_list[i].sps_name  = (char*) malloc ( 300 * sizeof(char) ) ;

bak_sps_list =  (Sptyp * ) malloc (MAXINDXSP * (sizeof (Sptyp))) ;
for (i= 0; i< MAXINDXSP; i ++)
   bak_sps_list[i].sps_name  = (char*) malloc ( 300 * sizeof(char) ) ;


strcpy (sps_list[0].sps_name, datamatrix[0].sps_name);
//sps_list[0].sps_name = datamatrix[0].sps_name ;
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
        strcpy(sps_list[ espec ].sps_name,datamatrix[i].sps_name) ;//sps_list[ espec ].sps_name = datamatrix[i].sps_name ;
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
   int cual=0,j,l,i ;
   Sptyp * pt_sp ;
   Conftyp * pt_conf;
   Punktyp * pt ;
   pt_sp = sps_list ;
   pt_conf = pt= datamatrix ;
  // fclose(output_file);
  // output_file= fopen("limites.tps", "w");

   for (  i = 0 ;   i < nuspecs ; i ++ ) {
      pt_sp[i].min_age = 10000000000 ;
      pt_sp[i].max_age = -1000000000 ;
      for (j = 0 ;  j < pt_sp[i].num_confs  ; j ++) {
        cual = pt_sp[i].conflist[j] ;
        pt_conf[cual].sp_number = pt_sp[i].sp_number ;
        if (pt_conf[cual].age < pt_sp[i].min_age ){
             pt_sp[i].min_age = pt_conf[cual].age ;
             pt_sp[i].confminage = cual; }
        if (pt_conf[cual].age > pt_sp[i].max_age ){
             pt_sp[i].max_age = pt_conf[cual].age ;
             pt_sp[i].confmaxage = cual; }
       }
      }

 }


void define_relative_ages (int nuspec   ) {
int i , j , cual = 0 ;
Conftyp * pt_conf ;
Sptyp * pt_sp ;

pt_conf= datamatrix ;
pt_sp = sps_list ;

for (  i = 0 ;   i < nuspec ; i ++ ) {
   for (j = 0 ;  j < pt_sp[i].num_confs  ; j ++) {
         cual = pt_sp[i].conflist[j] ;
         pt_conf[cual].std_sp_age =  (pt_conf[cual].age - pt_sp[i].min_age)  / (pt_sp[i].max_age - pt_sp[i].min_age)  ;
         cual ++ ; } }
}


double pair_conf_dist (Punktyp *  pt1, Punktyp * pt2)
{
  double score = 0  ;
  int i , nlan ;
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
          }
     limits[i][lims-1] = sps_list[i].max_age  ;
    }

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
          if (cual == pt_sp[i].confmaxage){
              pt_conf[cual].which_class = (nucats-1) ;
              yes [i][nucats-1] = 1 ;
              continue;}
          for (k = 0 ;  k < nucats  ; k ++)
          {
           if (timeas || dointerp)
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
      if ( unique && !(dointerp) ) {
        if (timeas){
          printf("\n The analysis cannot be performed with the number of stages defined");
          printf("\nNo obs for stage %i (%f-%f) species %i= %s",j,limits[i][j],limits[i][j+1],i,sps_list[i].sps_name);
          printf("\n");
           }
        else{
          printf("\nThe analysis cannot be performed");
          printf("\nNo obs for stage %i species %i",j,i);} }
        return (0) ; }
  return (1) ;
} // isthere_data_for_all_cats


void make_d_shifts (sp1,sp2,nucateg) {
int  i,   j,  k, dde = 0  , categ,w_besco, cat,move  ,guich,stg_star_m,stg_fin_m ;
Punktyp * pts_sp1, * pts_sp2, * ptf_sp1, * ptf_sp2, *pts_sp3 ;
double besco,dist_start,dist_end, score=0,core=0, penal  ;

             for (i = - ( nucateg - 4 ) ; i < ( nucateg - 4 )  ; i ++ ){
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
                     score = (dist_start + dist_end) / 2 ;
                     penal = penalty  * 2 ;
                     score = score +  penal  + ( penal * ( move - 1) * pen_ext) ;
                     sank_mtx[sp1][sp2].score_shft[ dde ] = score ;
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
                        k = -i;
                      else
                         k = i ;
                     score = score / (nucateg-k) ;
                     penal = penalty  * 2 ;
                     score = score +  penal  + ( penal * ( k - 1) * pen_ext) ;
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
 int a ,  b , c=0 , i , invertido = 0 ,d, sp1 , sp2,dde,  w_besco, j, total,move,k,e ;
 double besco= 9999999999, scor,score   ;
 Sank_spcelltyp ** sank_pt ;
 sank_pt = sank_mtx ;


 total = (NUCATEG - 3) * 2   ;

    for (a = 0; a < nuspecs; a++)
     {
        sp1 = a  ;
        dde = 0 ;

       for (i = ( - NUCATEG + 4 ) ; i <  NUCATEG -4  ; i ++ )
        {
          if (i == 0 ) continue ;
          translator_str [dde] = i ;
          if (( NUCATEG + i ) <  MINCATS){
             for (c=  0; c < nuspecs ; c ++ )
               sank_pt [c][sp1].score_str[dde] = -99999 ;
               dde ++ ;
             continue;}


          define_limit_stretch (  i , NUCATEG , sp1, invertido  ) ;
          if (sorting_confs_in_cats_stretch ( NUCATEG , nuspecs , CONFS, sp1 , i,0,0  ))
           {
            fill_w_consense_stretch (i ,NUCATEG, sp1,invertido,0) ;
            for (b = 0; b < nuspecs; b++)
              {

             if ( (b == 1) && (a == 5) && (i == 4))
                flag = 3 ;
               sp2 = b ;
               if ( sp1 == sp2 ) continue;
               fill_doc1_w_consense_asis ( sp2, NUCATEG  ) ;
               scor  =  score_in_docks ( NUCATEG , i, invertido,0 ) ;
               flag= 0 ;
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
for (a = 0 ; a < nuspecs ; a ++){
 for (b = a ; b < nuspecs ; b ++){
  if (a == b) continue ;
 // printf("\n END cambio Especie %i->%i +",a,b);
  for (d = 0 ; d < dde ; d ++){
   k = translator_str [d] ;
   for (e= 0 ; e < dde ; e++){
     j = translator_str [e] ;
     if (k == - j ){
      // printf("\n %i= %f / %f",k, sank_mtx[a][b].score_str [d], sank_mtx[b][a].score_str [e]);
       sank_mtx[a][b].score_str [d] =  sank_mtx[b][a].score_str [e] =  (sank_mtx[a][b].score_str [d] + sank_mtx[b][a].score_str [e]) / 2 ;
       }}}
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
         if ( besco  ==  99999999 ){
            sank_mtx[a][b].score_str[0 ] = besco ;
            w_besco = 0 ;  }
       sank_mtx[a][b].best_str = w_besco ;
       }
  }


}//make_d_stretchs_recat


make_inv_stretchs_recat (  ) {
 int a , b , c=0 , i, w ,d, sp1 , sp2,dde, invertido=1,  w_besco, move, adde,e,j,k  ;
 double besco= 9999999999, scor,score  ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
 Sank_spcelltyp ** sank_pt ;
 sank_pt = sank_mtx ;

pt_conf = datamatrix ;
pt_sp = sps_list ;




    for (a = 0; a < nuspecs; a++){
        sp1 = a  ;  dde = 0 ;
        for (i = - NUCATEG + 4    ; i < (NUCATEG - 4)    ; i ++ ){
          if (i == 0) continue ;
          translator_strinv [ dde ] = i ;
          if (( NUCATEG + i ) <  MINCATS) {
             for (c=  0; c < nuspecs ; c ++ )
               sank_pt [c][sp1].score_str_inv[dde] = -99999 ;
               dde ++ ;
               continue ; }
           /*if ( (a == 3) && (i == -15)  )
              flag = 1 ; */
               flag = 0 ;
           define_limit_stretch (  i , NUCATEG , sp1, invertido  ) ;
           if (sorting_confs_in_cats_stretch ( NUCATEG , nuspecs , CONFS, sp1 , i ,1,0 ))  // las pone en las categs de stret de 0 a x . voy a considerar q
           {                                                                            //se cuentan desde el final de la traject en o de las fciones
            fill_w_consense_stretch (i ,NUCATEG, sp1, invertido,0) ;
            for (b = 0; b < nuspecs; b++)
              {

               sp2 = b ;
               /*if (sp2 == 0  && flag == 1 )
                 flag = 2 ;*/

               if ( sp1 == sp2 ) continue;
               fill_doc1_w_consense_asis ( sp2, NUCATEG  ) ;
               scor  =  score_in_docks ( NUCATEG , i , invertido,0) ;
               flag = 0;
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




for (a = 0 ; a < nuspecs ; a ++){
 for (b = a ; b < nuspecs ; b ++){
  if (a == b) continue ;
  //printf("\n START cambio Especie %i->%i +",a,b);
  for (d = 0 ; d < dde ; d ++){
   k = translator_strinv [d] ;
   for (e= 0 ; e < dde ; e++){
     j = translator_strinv [e] ;
     if (k == - j ){
      // printf("\n %i= %f / %f",k, sank_mtx[a][b].score_str [d], sank_mtx[b][a].score_str [e]);
       sank_mtx[a][b].score_str_inv [d] =  sank_mtx[b][a].score_str_inv [e] =  (sank_mtx[a][b].score_str_inv [d] + sank_mtx[b][a].score_str_inv [e]) / 2 ;
      }}}
  } }



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
           if ( besco  ==  99999999 ){
             sank_mtx[a][b].score_str_inv[ 0 ]  = besco ;
             w_besco = 0 ;  }
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
 /* for (a= 0 ; a < dde ; a ++)
    translator_strinv [a] = - translator_strinv [a ] ;*///esto estaba en el codigo viejo. Ahora lo hago negativo para la izquierda
}//make_inv_stretchs_recat


make_shift_stretchs_recat (  ) {
int a, i , j , c ,d ,k,l,e, sp2, sp1,    mvs,mvf,finInv, starInv,star, fin;
int cto,  invertido = 2 , dde=0 ,w_besco, w ;
double scor, besco ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
Sank_spcelltyp ** sank_pt ;
sank_pt = sank_mtx ;
pt_conf = datamatrix ;
pt_sp = sps_list ;


// for (i = -  NUCATEG + 4      ; i < ( NUCATEG - 3)   ; i ++ ){
// for (j = -  NUCATEG + 4    ; j < ( NUCATEG - 3)   ; j ++ ){
 for (i = -  NUCATEG + 3      ; i < ( NUCATEG - 2)   ; i ++ ){
 for (j = -  NUCATEG + 3    ; j < ( NUCATEG - 2)   ; j ++ ){

         translator_sh_str [0] [dde] = i ;
         translator_sh_str [1] [dde] = j ;
       dde ++ ;}}

       for (sp1 = 0; sp1 < nuspecs; sp1++){ // lup de la especie a modificar
          for (d = 0 ; d < dde ; d++){
              i = translator_sh_str [0][ d ] ;
              j = translator_sh_str [1][ d ] ;


              if (!accept_sh_str(i,j,sp1) ){
                for (c=  0; c < nuspecs ; c ++ )
                 sank_pt [c][sp1].score_sh_str[d] = -99999 ;
                  continue ;
                 }

              define_limit_db_stretch(i,NUCATEG,sp1,j) ; // cambio_izq,Ncateg,spamodif,cambio_der)
           cto = -i + j ;
           if (sorting_confs_in_cats_stretch ( NUCATEG , nuspecs , CONFS, sp1 , i,invertido,j  ))  // las pone en las categs de stret de 0 a x . voy a considerar q
           {                                                                            //se cuentan desde el final de la traject en el resto de las fciones
            fill_w_consense_stretch (i ,NUCATEG, sp1, invertido,j) ;
            for (sp2 = 0; sp2 < nuspecs; sp2++)
              {
                flag =  0 ;
               if ( (sp2 == 1) && (sp1 == 5) && (i == -5) && (j == 4) )
                   flag = 2 ;
               if ( sp1 == sp2 ) continue;
               fill_doc1_w_consense_asis ( sp2, NUCATEG  ) ;
               scor  =  score_in_docks ( NUCATEG , i , invertido,j) ;
               flag = 0 ;
               mvs = i ; mvf = j ;
               if (( mvs > 0 && mvf > 0 ) || ( mvs > 0 && mvf > 0 )) {
                 if (mvs < 1) mvs = - mvs ;
                 if (mvf < 1) mvf = - mvf ;
                 if (mvf >= mvs ){k = mvf  ;  l = k + (mvf-mvs); }
                 if (mvs > mvf ) { k = mvs ;  l = k + (mvs-mvf);}
                 //scor = scor + penalty +( penalty * ( l - 1) * pen_ext)  ;
                   scor = scor + penalty * ( mvs + mvf ) ;
                 sank_pt [sp2][sp1].score_sh_str[ d ] = scor ;
               }
                else
                  {
                  if (mvs < 1) mvs = - mvs ;
                  if (mvf < 1) mvf = - mvf ;
                  l = mvs + mvf ;
                  //scor = scor + penalty +( penalty * ( l - 1) * pen_ext) ;//
                  scor = scor + penalty * ( mvs + mvf ) ;
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


for (a = 0 ; a < nuspecs ; a ++){
 for (b = a ; b < nuspecs ; b ++){
  if (a == b) continue ;
  for (d = 0 ; d < dde ; d ++){
   star = translator_sh_str [0][d] ;
   fin  = translator_sh_str [1][d] ;
   for (e= 0 ; e < dde ; e++){
     starInv = translator_sh_str [0][e] ;
     finInv  = translator_sh_str [1][e] ;
     if ((star == - starInv ) && ( fin == - finInv) ) {
       if ( (sank_mtx[a][b].score_sh_str [d] > 0) && (sank_mtx[b][a].score_sh_str  [e] > 0) )
         sank_mtx[a][b].score_sh_str [d] =  sank_mtx[b][a].score_sh_str  [e] =  (sank_mtx[a][b].score_sh_str [d] + sank_mtx[b][a].score_sh_str [e]) / 2 ;
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
         if ( besco  ==  99999999 ){
             sank_mtx[a][b].score_sh_str[ 0 ]  = besco ;
             w_besco = 0 ;  }
       sank_mtx[a][b].best_sh_str = w_besco ;
     }
  }

   w_besco = sank_mtx[1][5].best_sh_str ;
   star = translator_sh_str [0][w_besco] ;
   fin  = translator_sh_str [1][w_besco] ;
//printf("BEST %i,%i,%f\n",star,fin,sank_mtx[1][5].score_sh_str[w_besco]) ;



}//make_shift_stretchs_recat




int accept_sh_str(int i,int j,int spss ){
int  span1,span2 ;


     if ( i == j  )  // que no dividamos en menos de 4 toda la categoria
          return (0);

    if ( ( NUCATEG -i + j ) < MINCATS )  // que no dividamos en menos de 4 toda la categoria
                   return (0);

      if ((i == 0) || (j==0 )  || (j==i))
        return (0) ;
       //   ACA ME FIJO CUANTAS CATEGS DE LA SP MODIFICADA QUEDAN
       span1 =  NUCATEG - i + j ;
       span2 =  NUCATEG ;
       if ( i > 0 && j > 0 )
         if ( (NUCATEG - j - i ) < 4 ) // se comparan menos que 4 originales
           return (0);
       if ( i < 0 && j < 0 )
         if ( ( NUCATEG + j + i ) < 4 ) // se comparan menos que 4 originales
           return (0);
       if ( i < 0 && j > 0 )
          if (( NUCATEG +i - j) < 4  ) // se comparan menos que 4 originales
            return (0);
       if ( i > 0 && j < 0 )
          if ( span1 < MINCATS ) {
          // printf("\n%i/%i RECHAZADO POR una traject muy corta en la sp modificada categs ",i,j) ;
           return (0) ;}
       // ESTOS SON SOBRE EXTENSION DE UNO SOBRE EL OTRO
       if (  span2 > span1)
        if (span2/span1 >= 4 ){
          return (0) ;}
        else
         if ( span1/span2 >= 4 )
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


int read_data_mj () {
char  buffer [MAX_x_LINE] ;
char ind_name [200] ;
int pos, a;

fgets (buffer,50000,input_file) ;
for (a = 0 ; a < CONFS; a++){
    fgets (buffer,50000,input_file) ;
    save_configuration_mj (a, DIMS, LANDS, buffer ) ;
    }

 nuconfs = a ;
 nuspecs =  count_species ( nuconfs ) ;

 if (nuspecs < 4 ){
   printf ("\n Error: less than four species in dataset ");
   fflush(stdout) ;
 return (0) ;}
return (1);
}//read_data_mj ()

int save_configuration_mj(int guichconf,int dime,int nland, char * bafer ){
 int l = 0,i,  ctos, rsd = 0  , j,pos,u, cut = 0,m ,k ;
 double * pt_edad ;
 char  * pt_spname,  * pt_char, iname[300],ind_info[300],  * pt_orig  ;
 Punktyp * pt = datamatrix[guichconf].pt ;
 pt_spname = datamatrix[guichconf].sps_name  ;
 pt_edad=& datamatrix[guichconf].age ;
 datamatrix[guichconf].confnumber = guichconf ;
 datamatrix[guichconf].nulands = nland ;
 pt_char = bafer ;
// separa= " " ;

 pt_orig = bafer ;
 while (!isspace(* pt_char))
      pt_char ++ ;
  pos =  pt_char - bafer ;
  strncpy (iname, bafer,pos);
  if ( strchr ( iname , '/' )  == NULL ){
   for (i = 0 ; i < pos; i ++)
     if (iname[i]> 47 && iname[i]< 58 ){
       iname [i] = '\0' ; cut = 1 ;
       break ; }
   if (!cut)
       iname [pos] = '\0' ;
   strcpy(datamatrix[guichconf].sps_name,iname)  ;
   datamatrix[guichconf].sps_name[pos+1] ='\0' ;
  }
  else{
   for ( j = 0 ; j < pos ; j++){
     if (iname[j] == '/'){
       iname[j]   = '\0' ;
       m = 0 ;
       j++ ;
       for (k = j ; k < pos ;k++){
        ind_info [m] = iname[k] ;
        m++;}
       ind_info [m] = '\0' ;
       strcpy (datamatrix[guichconf].ind_number, ind_info) ;
       break ;
       }
     strcpy(datamatrix[guichconf].sps_name,iname)  ;
     datamatrix[guichconf].sps_name[j+1] ='\0' ;}
            }



  pt_char = strtok(bafer," \t\r\n\f\v");
  if (!old_mj){
  pt_char = strtok(NULL," \t\r\n\f\v");
  datamatrix[guichconf].age = strtod ( pt_char,NULL); }
  for (l = 0 ; l < nland  ; l ++ ) {
      pt_char = strtok(NULL," \t\r\n\f\v");  pt->x = strtod ( pt_char,NULL);
      pt_char = strtok(NULL," \t\r\n\f\v");  pt->y = strtod ( pt_char,NULL);
     if (DIMS == 3){
       pt_char = strtok(NULL," \t\r\n\f\v"); pt->z = strtod ( pt_char,NULL);}
     pt++;  }
 if (old_mj) {
  pt_char = strtok(NULL," \t\r\n\f\v");
  datamatrix[guichconf].age = strtod ( pt_char,NULL); }



return (1);
}


int  read_data () {
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
              printf ("\nError! Line \"LM=\" not found (approx. line %i)",contlin);
             return (0); }
             for(i = 0; i<100; i++)
               stri[i] = tolower(buffer[i]);
             //if (( strstr(buffer,"LM=" ) != NULL ) || ( strstr(buffer,"LM3=" ) != NULL )) {  //FLAG
            if (( strstr(stri,"lm=" ) != NULL ) || ( strstr(stri,"lm3=" ) != NULL )) {  //FLAG
                if (save_configuration ( a, DIMS, LANDS, buffer ) )
                   printf("");
                 else{
                  printf ("\n Error reading the data, approx. line %i ", contlin);
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
}//

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
 read_next_line ( biffer) ; //ver
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


void dealloc_datamatrix (  ) {
 int   h, especimens;
 if (  dointerp  )
   especimens = CONFS + ( nuspecs * CAT_INTER) ;
 else
   especimens = CONFS ;
 for ( h = 0;  h < especimens ; h++ )
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

bak_consense_matrix = malloc ( nuno * categs * sizeof(Conftyp *) ) ;
 for (h = 0; h < nuno  ; h++ ){
     bak_consense_matrix[h] = malloc (categs * sizeof (Conftyp ));
       for ( i = 0 ; i < categs; i ++) {
          bak_consense_matrix [ h ][ i ].pt = (Punktyp *) malloc ( nuland * sizeof(Punktyp)) ;} }





 }


void alloc_interp_trajec ( ) {
 int  i, h ;
 interp_trajec = malloc ( nuspecs * CAT_INTER * sizeof(Conftyp *) ) ;
 for (h = 0; h < nuspecs  ; h++ ){
     interp_trajec[h] = malloc (CAT_INTER * sizeof (Conftyp ));
       for ( i = 0 ; i < CAT_INTER; i ++) {
          interp_trajec [ h ][ i ].pt = (Punktyp *) malloc ( LANDS * sizeof(Punktyp)) ;} }

 }







void alloc_optimus_matrix (int stados, int categs, int nuland  ) {
 int  i, h ;
 optimus_matrix = malloc ( stados * categs * sizeof(Conftyp *) ) ;
 for (h = 0; h < stados  ; h++ ){
     optimus_matrix[h] = malloc (categs * sizeof (Conftyp ));
       for ( i = 0 ; i < categs; i ++) {
          optimus_matrix [ h ][ i ].pt = (Punktyp *) malloc ( nuland * sizeof(Punktyp)) ;} }

 }

void alloc_consense_disparity (){
 int i ;
  consense_dispar =  malloc (CATALINS * sizeof (Conftyp ));
   for ( i = 0 ; i < CATALINS; i++)
       consense_dispar [ i ].pt = (Punktyp *) malloc ( LANDS * sizeof(Punktyp)) ;
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
 color_labels = malloc   ( (2 * nt) * sizeof(char*) ) ;
 back_labels = malloc ( ( 2 * nt) * sizeof(char*) ) ;
 for (i = 0; i < ( 2 * nt ); i ++){
   branch_labels[i]  = malloc ( 300 * sizeof(char) ) ;
   cats_labels[i]  = malloc ( 300 * sizeof(char) ) ;
   color_labels[i]  = malloc ( 300 * sizeof(char) ) ;
   back_labels[i]  = malloc ( 300 * sizeof(char) ) ;}
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
      define_final_states ( nodo ) ; // aca llena all_trans de nodos internos
           }
 for ( n = 0 ; n < nt  ;n ++)
     final_states[n][n] = 1 ;

complete_all_trans (); // aca llena all_trans de terminales


for (n=0 ; n < nnods ; n++){
   all_trans[n][5] = 0 ;
   for (i = 0 ; i < 5 ; i++)
      if (all_trans[n][i] != 0 )
          all_trans[n][5] ++ ;}


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
int  n, st_anc, e, nodo, st_nod , optstate, i ;
double mincore, score ;
if ( recons   == NULL)
  alloc_recons ( ) ;

for ( n = intnods  ;  n -- ; ){
 nodo = optlist [n] ;
 if (nodo == nt ){
     if (OUTGRP < nt)
       recons[0][nt] = OUTGRP;
     else
       for (e = 0 ; e < STATES ; e ++)    //ACA TENGO QUE ELEGIR SIEMPRE EL MISMO Y SER CONSECUENTE EN TODO EL PROGRAMA
        if (final_states [nodo][e] == 1){
         recons[0][ nodo ] = e ; break;}
   }
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

if (OUTGRP > nt && all_trans[OUTGRP][5] > 1)
  recons[0][nt] = recons[0] [OUTGRP];


  score =  0;
  for (n =  0 ; n < nnods ; n++ )
   {
   if (n == nt)                                  // if (n == nt) continue ; // SI TOY EN LA RAIZ
     continue ;
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
int lims,   j  ,  vani=0 ;
double span ;
lims = sup_limit [guichsp] - inf_limit [guichsp] + 1 ;
   span = ( sps_list[guichsp].max_age - sps_list[guichsp].min_age )  / ( lims - 1 );
   printf("\nLimites alineamiento Especie %i ",guichsp);
   for (j = inf_limit[guichsp] ; j < sup_limit [guichsp] + 1 ; j ++ ){
    limits_aln [guichsp][j] = sps_list[guichsp].min_age + (  span * vani )  ;
    printf("%f ",limits_aln [guichsp][j]);
    vani++;}
limits_aln[guichsp][sup_limit[guichsp]] = sps_list[guichsp].max_age ;


}



void alloc_alignment (int totcats, int nuspecs ){
int h,i ;
  free (align_matrix) ;
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
           if  (k == sup_limit [guichsp]){
              pt_conf[cual].which_aln_class = k ;
              continue ; }
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
    strcpy(qqqstr,"tnt  ") ; //tiene que ir el nombre del archivo y el del script separado por ;
    strcat (qqqstr,outputFilename) ;
    strcat (qqqstr," chg_2tnt.tmp") ;

    startinfo.cb = sizeof(STARTUPINFO);
    startinfo.lpReserved = NULL;
    startinfo.lpDesktop = NULL;
    wsprintf(jstr,"RUNNING TNT");
    startinfo.lpTitle = jstr;
    startinfo.dwFlags = STARTF_USESHOWWINDOW;
    //startinfo.dwFlags = STARTF_USEPOSITION | STARTF_USESIZE ;
    startinfo.dwX = 25 ;      /*50*/
    startinfo.dwXSize = 350 ; /*700*/
    startinfo.dwY = 50;      /*100*/
    startinfo.dwYSize = 125 ;  /* 250*/
    startinfo.cbReserved2 = NULL;
    startinfo.wShowWindow = SW_HIDE;
       /*if(CreateProcess(NULL, qqqstr, NULL, NULL, FALSE ,
            HIGH_PRIORITY_CLASS | 0, NULL, NULL, &startinfo, &pinfo))*/
       if(CreateProcess(NULL, qqqstr, NULL, NULL, FALSE ,
            CREATE_NO_WINDOW , NULL, NULL, &startinfo, &pinfo))
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
    startinfo.dwFlags = STARTF_USESHOWWINDOW;
    //startinfo.dwFlags = STARTF_USEPOSITION | STARTF_USESIZE ;
    startinfo.dwX = 25;
    startinfo.dwXSize = 350 ;
    startinfo.dwY = 50 ;
    startinfo.dwYSize = 125 ;
    startinfo.cbReserved2 = NULL;

    startinfo.wShowWindow = SW_HIDE;

       if(CreateProcess(NULL, qqstr, NULL, NULL, FALSE ,
            CREATE_NO_WINDOW , NULL, NULL, &startinfo, &pinfo))
      /* if(CreateProcess(NULL, qqstr, NULL, NULL, FALSE ,
            HIGH_PRIORITY_CLASS | 0, NULL, NULL, &startinfo, &pinfo))*/

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
    startinfo.dwFlags = STARTF_USESHOWWINDOW;
    //startinfo.dwFlags = STARTF_USEPOSITION | STARTF_USESIZE ;
    startinfo.dwX = 25 ;
    startinfo.dwXSize = 350 ;
    startinfo.dwY = 50 ;
    startinfo.dwYSize = 125 ;

    startinfo.cbReserved2 = NULL;
    startinfo.wShowWindow = SW_HIDE;
       if(CreateProcess(NULL, qqqstr, NULL, NULL, FALSE ,
            CREATE_NO_WINDOW , NULL, NULL, &startinfo, &pinfo))
       /*if(CreateProcess(NULL, qqqstr, NULL, NULL, FALSE ,
            HIGH_PRIORITY_CLASS | 0, NULL, NULL, &startinfo, &pinfo))*/
        WaitForSingleObject(pinfo.hProcess,INFINITE);
            else {
                MessageBox(hwnd,"TNT could not be started!","TNT executable should be is in the same folder than SPASOS",MB_OK | MB_ICONERROR );
                return(255);
            }
        GetExitCodeProcess(pinfo.hProcess, &how);
        return( how );
}



void fill_consense_matrix ( int espec, int nucats, int nuland  ){
int i, j ,k,  nulan, l,  son , a,s,c ;
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


int fill_bak_consense_matrix (  int espec, int nucats, int nuland  ){
int  j , l, a ;

for  ( a = 0 ; a < espec ; a ++ ) {
  for (j= 0 ;  j < nucats  ; j ++) {
   for (l = 0 ; l < nuland ; l++){
      bak_consense_matrix [a][j].pt[l].x  = consense_matrix [ a ][ j ].pt[l].x;
      bak_consense_matrix [a][j].pt[l].y  = consense_matrix [ a ][ j ].pt[l].y;
      if (DIMS ==3)
       bak_consense_matrix [a][j].pt[l].z  = consense_matrix [ a ][ j ].pt[l].z;}}}
}

int restitute_consense_matrix (  int espec, int nucats, int nuland  ){
int i, j , l,  a ;

for  ( a = 0 ; a < espec ; a ++ ) {
  for (j= 0 ;  j < nucats  ; j ++) {
   for (l = 0 ; l < nuland ; l++){
      consense_matrix [a][j].pt[l].x  = bak_consense_matrix [ a ][ j ].pt[l].x;
      consense_matrix [a][j].pt[l].y  = bak_consense_matrix [ a ][ j ].pt[l].y;
      if (DIMS ==3)
       consense_matrix [a][j].pt[l].z  = bak_consense_matrix [ a ][ j ].pt[l].z;}}}
}


void map_changes (int qreco, int resampling){  // Agrega los cambios en branch_labels, llena transformations y guich_map. Si resample entonces llena tranform_rnd y guich_rnd cdo resampling

int n,  shift,stre,std_anc,std_nod,stra,stri, num, sign, sig,resa ;
Sank_spcelltyp ** pt_sank ;
char etiqueta [50], numero [5], numerob[5];
numero [0] = NULL ;
numerob[0] = NULL;

resa = resampling ;

pt_sank = sank_mtx ;
fflush(stdout);


 for (n =  0 ; n < nnods ; n++ )
 {
     etiqueta [0] = NULL;

 if (n == nt){
     if (resampling == 0 ){
      itoa(n,numero,10);
      strcpy (etiqueta,numero) ;
      strcat (etiqueta,"_") ;
      strcat (etiqueta,"_") ;
      strcat (branch_labels[n],etiqueta);}
      }
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
          easy_trans_rnd[resa][n][0] = 0; easy_trans_rnd[resa][n][1] = 0;
         }
        else{
          transformations [n] = 0 ;
          easy_trans[n][0] = 0 ; easy_trans[n][1] = 0;
          if (resampling == 0 ){
           strcat(etiqueta,"/");    //
           itoa(std_nod,numero,10); //
           strcat (etiqueta,numero); //
           strcpy (branch_labels[n],etiqueta);}
         }
       }
   else
    if ( pt_sank[std_anc][std_nod].what_best == 1 ){//shift es uno
      if (resampling > 0){
          transform_rnd [n] [resampling-1] = 1 ;
        }
      else
        transformations [n] = 1 ;
      shift=  pt_sank[std_anc][std_nod].best_shft ;
      shift = translator_sh [shift] ;
      if (resampling > 0){
          guich_rnd [n][resampling-1] = shift ;
          easy_trans_rnd[resa][n][0] = shift; easy_trans_rnd[resa][n][1] = shift;
          }
      else {
          guich_map [n] = shift ;
          easy_trans[n][0] = shift; easy_trans[n][1] = shift;
          if (resampling ==  0) {
           strcat (etiqueta,"Shi_") ;
           itoa(shift,numero,10);
           strcat(etiqueta,numero);
           strcat(etiqueta,"/");    //
           itoa(std_nod,numero,10); //
           strcat (etiqueta,numero); //
           strcpy (branch_labels[n],etiqueta);}

     }
     }
    else
     if ( pt_sank[std_anc][std_nod].what_best == 2 ){// stre es dos
       if (resampling > 0)
          transform_rnd [n] [resampling-1] = 2 ;
        else
          transformations [n] = 2 ;
        itoa(std_nod,numero,10);
        stre=  pt_sank[std_anc][std_nod].best_str ;
        stre = translator_str [stre] ;
        if (resampling > 0 ){
         guich_rnd [n][resampling-1] = stre ;
         easy_trans_rnd[resa][n][0] = 0 ; easy_trans_rnd[resa][n][1] = stre ;
         }
        else{
         guich_map [n] = stre ;
         easy_trans[n][0] = 0 ; easy_trans[n][1] = stre ;
         if (resampling == 0 ){
          strcat (etiqueta,"StrE_") ;
          itoa(stre,numero,10);
          strcat(etiqueta,numero);
          strcat(etiqueta,"/");    //
          itoa(std_nod,numero,10); //
          strcat (etiqueta,numero); //
          strcpy (branch_labels[n],etiqueta);}

      }
        }
    else
     if ( pt_sank[std_anc][std_nod].what_best == 3 ){// stresart es tres
       if (resampling > 0)
          transform_rnd [n][resampling-1] = 3 ;
        else
         transformations [n] = 3 ;
        stre=  pt_sank[std_anc][std_nod].best_stri ;
        stre = translator_strinv [stre] ;
        if (resampling > 0 ){
         guich_rnd [n][resampling-1] = stre ;
         easy_trans_rnd[resa][n][0] = stre ; easy_trans_rnd[resa][n][1] = 0 ; }
        else{
         guich_map [n]  = stre ;
         easy_trans[n][0] = stre ; easy_trans[n][1] = 0  ;
         if (resampling == 0 ){
          strcat (etiqueta,"StreS_") ;
          itoa(stre,numero,10);
          strcat(etiqueta,numero);
          strcat(etiqueta,"/");    //
          itoa(std_nod,numero,10); //
          strcat (etiqueta,numero); //
          strcpy (branch_labels[n],etiqueta);}

      }
     }
    else
      if ( pt_sank[std_anc][std_nod].what_best == 4 ){
       if (resampling > 0)
          transform_rnd [n][resampling-1] = 4 ;
        else
         transformations [n] = 4 ;
        stri=  pt_sank[std_anc][std_nod].best_sh_str ;
        stre  = translator_sh_str [0][stri] ;
        stra  = translator_sh_str [1][stri] ;
        itoa(stre,numero,10);
        itoa(stra,numerob,10);
        if (resampling > 0){
          guich_rnd [ n ][resampling-1] = stre ;
          guich_rnd [ n + MAXNODES ][resampling-1] = stra ;
          easy_trans_rnd[resa][n][0] = stre ; easy_trans_rnd[resa][n][1] = stra ;
          }
        else {
          guich_map[ n ] = stre ;
          guich_map[ n + MAXNODES ] = stra ;
          easy_trans[n][0] = stre ; easy_trans[n][1] = stra ;
          if (resampling == 0 ){
           strcat (etiqueta,"Dstre_") ;
           strcat(etiqueta,numero);
           strcat(etiqueta,"_");
           strcat(etiqueta,numerob);
           strcat(etiqueta,"/");    //
           itoa(std_nod,numero,10); //
           strcat (etiqueta,numero); //
           strcpy (branch_labels[n],etiqueta);}

       }
      }
     }
   }
 }
improve_map_changes (resampling) ;

}//map_changes

void map_changes_perc (int qreco, int resampling, int continu){

int n,  sign,std_nod;
double doble,shift, stre,stra,stri ;
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
  if(opt_asis == 1 )
      itoa(n,numero,10);
  else {
   if (easy_trans[n][0] == 0  && easy_trans[n][1] == 0   ){//( transformations[n] == 0 ){// 0 es as is
         branch_labels[n][0]= '\0' ;
       }
   else
    if  ( easy_trans[n][0] == easy_trans[n][1] ){//( transformations[n] == 1 ){//shift es uno
      branch_labels[n][0]= '\0' ;
      //strcat (etiqueta,"Shi_") ;
      shift=  trans_corr[0][n]  ;
      if (continu)
        doble =  shift / (sup_limit_cont[ances [n]] - inf_limit_cont[ances [n] ]);
      else
        doble =  shift / (sup_limit[ances [n]] - inf_limit [ances [n]] );

      doble = doble * 100;
      doble *= 10. ;
      shift = doble;
      doble= (double)shift / 10. ;
      shift = (int) doble;
      itoa(shift,numero,10);
      strcat(etiqueta,numero);
      strcat(etiqueta,"%|");
      strcat(etiqueta,numero);
      strcat(etiqueta,"%");
      strcpy (branch_labels[n],etiqueta);
     }
    else
    if ( easy_trans[n][0] == 0  && easy_trans[n][1] != 0   ){// if ( transformations[n] == 2 ){// stre es dos
        branch_labels[n][0]= '\0' ;
        itoa(std_nod,numero,10);
        //strcat (etiqueta"StrE_") ;
        doble = trans_corr [0][n];
        doble = doble / (sup_limit_cont[ances[n]] - inf_limit_cont[ances[n] ]);
        doble = doble * 100;
        doble *= 10. ;
        stre = doble;
        doble= (double)stre / 10. ;
        stre =(int) doble;
        itoa(stre,numero,10);
        strcat(etiqueta,"0%");
        strcat(etiqueta,"|");
        strcat(etiqueta,numero);
        strcat(etiqueta,"%");
        strcpy (branch_labels[n],etiqueta);
         }
    else
       if ( easy_trans[n][0] != 0  && easy_trans[n][1] == 0   ){ //if ( transformations[n] == 3 ){// streinv es dos
        branch_labels[n][0]= NULL ;
        //strcat (etiqueta,"StreS_") ;
        doble = trans_corr [0][n];
        doble = doble / (sup_limit_cont[ances[n]] - inf_limit_cont[ances[n] ]);
        /*if (continu)
        stre=  pt_sank[std_anc][std_nod].best_stri ;
         stre = translator_strinv [stre] ;
          doble = ((double) stre) / (sup_limit_cont[ances [n]] - inf_limit_cont[ances [n] ]);
        else
          doble = ((double) stre) / (sup_limit[ances [n]] - inf_limit [ances [n]] );*/
        doble = doble * 100;
        doble *= 10. ;
        stre = doble;
        doble= (double)stre / 10. ;
        stre =(int) doble;
        itoa(stre,numero,10);
        strcat(etiqueta,numero);
        strcat(etiqueta,"%|");
        strcat(etiqueta,"0");
        strcat(etiqueta,"%");
        strcpy (branch_labels[n],etiqueta);
        }
    else
      if ( easy_trans[n][0] != 0  && easy_trans[n][1] != 0   ){ //if ( transformations[n] == 4 ){
        branch_labels[n][0]= '\0' ;
        //strcat (etiqueta,"Dstre") ;
        doble = trans_corr [0][n];
        doble = doble / (sup_limit_cont[ances[n]] - inf_limit_cont[ances[n] ]);
        doble = doble * 100;  doble *= 10. ;  stre = doble;
        doble= (double)stre / 10. ;  stre =(int) doble;
        itoa(stre,numero,10);
        strcat(etiqueta,numero);
        strcat(etiqueta,"%|");
        doble = trans_corr [1][n];
        doble = doble / (sup_limit_cont[ances[n]] - inf_limit_cont[ances[n] ]);
        doble = doble * 100;  doble *= 10. ;  stra = doble;
        doble= (double)stra / 10. ;  stra =(int) doble;
        itoa(stra,numero,10);
        strcat(etiqueta,numero);
        strcat(etiqueta,"%");
        strcpy (branch_labels[n],etiqueta);
       }
      }
     }
   }
}//map_changes_percentage






void check_ambiguity (){

int n ;
int i;


if (bak_all_trans[sis[OUTGRP]][5]){
  printf("\r                                                                                         ");
  printf("\nWARNING: Ambiguity  inferred at the base of the tree. Change in developmental timing");
  printf("\n         assigned to one of the descending branches ");}
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


// fprintf(output_file,"\nwarn-;\nsil=all;\nmacro=;\nreport-; \ncls;\ntable/7;\nclb;\n");
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
      generate_d_svg(cats,0,-1,0);
    fclose (input_file) ;// lee el tmp para traducir los nodos

    if (!read_tmp_data ( cats,0  )){
      printf("\nLa cagamos Carlos");
    if (dodisparity)
      calculate_disparity (cats);
      calculate_chg_hetero_adults () ; // busco determinar la proporcion del cambio en bebes y en adultos que se debe a heterocronia
      return (0); }
remove ("chg_2tnt.tmp");
remove ( "chg_2pasos.tmp" );
remove ("trans.tmp") ;
generate_tps_shift (cats) ;

if (do_classif)
 generate_species_classif_recat (cats );

return (cats)       ;
} //generate_alignment_shift



calculate_chg_hetero_adults (){
int n, nodo,pos_nod,pos_des, d ,skip;
Punktyp  *pt_sp1, *pt_sp2 ;
double dist_horiz= 0, dist_vert = 0,dist_asis=0,span ;
printf("\n\nCambios en Adultos");
printf("\nNodoTNT nodo CompH horiz CompV vert DistAsis");
for ( n = intnods  ;  n -- ; ){
   nodo = optlist [n] ;
   pos_nod = sup_limit_cont[nodo] - 1 ;
  for (d = firs[nodo] ; d != - 9  ; d = sis [ d  ] ){
    pos_des = sup_limit_cont[d] - 1 ;
    pt_sp1 = optimus_matrix[nodo][pos_nod].pt ;
    pt_sp2 = optimus_matrix[d][pos_des].pt ;
    chg_asis [d]= pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
    printf("\n%i %f",nod_p2t[d],chg_asis[d]);
    dist_asis += chg_asis[d] ;
    if (pos_nod == pos_des){
     pt_sp1 = optimus_matrix[nodo][pos_nod].pt ;
     pt_sp2 = optimus_matrix[d][pos_des].pt ;
     horiz[d] = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
     vert[d]= 0 ;
     comp_vert  [d] = 0 ;
     comp_horiz  [d] = chg_asis[d] ;
     //printf("\nNo hay cambio de posicion en nodo  %i %i",d,nod_p2t[d]);
       }
     else{
      if (pos_nod < pos_des){//  Si el desc se extiende -> calculo horizontal entre el adulto del nodo y el joven alineado del desc. y el vertical con el descendiente
         pt_sp1 = optimus_matrix[nodo][pos_nod].pt ;
         pt_sp2 = optimus_matrix[d][pos_nod].pt ;
         horiz[d] = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
         pt_sp1 = optimus_matrix[d][pos_des].pt ;
         pt_sp2 = optimus_matrix[d][pos_nod].pt ;
         vert[d] = pair_conf_dist ( pt_sp1 , pt_sp2 ) ; }
        else{    //  Si el  desc se acorta calculo el horizontal entre el adulto del desc y el corresp del nood. Y calculo el vertical sobre el nodo
         pt_sp1 = optimus_matrix[nodo][pos_des].pt ;
         pt_sp2 = optimus_matrix[d][pos_des].pt ;
         horiz[d] = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
         pt_sp1 = optimus_matrix[nodo][pos_nod].pt ;
         pt_sp2 = optimus_matrix[nodo][pos_des].pt ;
        }
        skip = 0;
       if (vert[d] >= chg_asis [d] )
        if (vert[d] - chg_asis [d] < 0.0000000001 && horiz[d] < 0.000000001 ){
         comp_horiz[d] = 0 ; comp_vert[d]=vert[d] ;
         skip = 1 ; }
       if (vert[d] <= chg_asis [d] )
        if (chg_asis [d] - vert[d] <  0.0000000001 && horiz[d] < 0.000000001){
        comp_horiz[d] = 0 ; comp_vert[d]=vert[d] ;
         skip =1 ; }
     if (!skip){
       comp_horiz [d] =  (((horiz[d] * horiz[d]) + (chg_asis[d] * chg_asis[d]) - (vert[d] * vert[d])) / (2 * horiz[d] * chg_asis[d]) ) * horiz[d] ;
       if (comp_horiz [d]< 0 ){
         comp_horiz [d]= chg_asis[d] ;
       comp_vert[d] = 0 ; }
      else
       comp_vert  [d] = (chg_asis[d] - comp_horiz [d] ) ; }

    }
    dist_vert+=comp_vert[d] ;
    dist_horiz+=comp_horiz [d] ;
    /*printf("\n%i %i %f %f %f %f %f",nod_p2t[d],d,comp_horiz[d],horiz[d],comp_vert[d],vert[d],chg_asis[d]);*/
  }
}
/*printf("\nTotal: DistH=%f DistV=%f DistASIS=%f",dist_horiz,dist_vert,dist_asis) ;*/

fflush(stdout);
return (0);
}

calculate_chg_hetero_newborns (){
int n, nodo,pos_nod,pos_des, d,skip ;
Punktyp  *pt_sp1, *pt_sp2 ;
double dist_horiz= 0, dist_vert = 0,dist_asis=0 ;
printf("\n\nCambios en newborns");
 printf("\nNodoTNT nodo CompH horiz CompV vert DistAsis");
for ( n = intnods  ;  n -- ; ){
  nodo = optlist [n] ;
  pos_nod = inf_limit_cont[nodo] ;
  for (d = firs[nodo] ; d != - 9  ; d = sis [ d  ] ){
    pos_des = inf_limit_cont[d]  ;
    pt_sp1 = optimus_matrix[nodo][pos_nod].pt ;
    pt_sp2 = optimus_matrix[d][pos_des].pt ;
    chg_asis [d]= pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
    dist_asis += chg_asis[d] ;  ///*****
    if (pos_nod == pos_des){
      pt_sp1 = optimus_matrix[nodo][pos_nod].pt ;
      pt_sp2 = optimus_matrix[d][pos_des].pt ;
      horiz[d] = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
      vert[d]= 0 ;
      //dist_horiz+=horiz[d];
      comp_vert  [d] = 0 ;
      comp_horiz  [d] = chg_asis[d] ;
      //printf("\nNo hay cambio de posicion en nodo  %i %i",d,nod_p2t[d]);
      }
    else{
      if (pos_des < pos_nod){//  Si el desc se extiende -> calculo horizontal entre el adulto del nodo y el joven alineado del desc. y el vertical con el descendiente
         pt_sp1 = optimus_matrix[nodo][pos_nod].pt ;
         pt_sp2 = optimus_matrix[d][pos_nod].pt ;
         horiz[d] = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
         pt_sp1 = optimus_matrix[d][pos_des].pt ;
         pt_sp2 = optimus_matrix[d][pos_nod].pt ;
         vert[d] = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
        }
        else{    //  Si el  desc se acorta calculo el horizontal entre el adulto del desc y el corresp del nood. Y calculo el vertical sobre el nodo
         pt_sp1 = optimus_matrix[nodo][pos_des].pt ;
         pt_sp2 = optimus_matrix[d][pos_des].pt ;
         horiz[d] = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
         pt_sp1 = optimus_matrix[nodo][pos_nod].pt ;
         pt_sp2 = optimus_matrix[nodo][pos_des].pt ;
         vert[d] = pair_conf_dist ( pt_sp1 , pt_sp2 ) ;
         }
         skip =0;
       skip = 0;
       if (vert[d] >= chg_asis [d] )
        if (vert[d] - chg_asis [d] < 0.0000000001 && horiz[d] < 0.000000001 ){
         comp_horiz[d] = 0 ; comp_vert[d]=vert[d] ;
         skip = 1 ; }
       if (vert[d] <= chg_asis [d] )
        if (chg_asis [d] - vert[d] <  0.0000000001 && horiz[d] < 0.000000001){
        comp_horiz[d] = 0 ; comp_vert[d]=vert[d] ;
         skip =1 ; }
     if (!skip){
       comp_horiz [d] =  (((horiz[d] * horiz[d]) + (chg_asis[d] * chg_asis[d]) - (vert[d] * vert[d])) / (2 * horiz[d] * chg_asis[d]) ) * horiz[d] ;
       if (comp_horiz [d]< 0 ){
         printf("\ncomp horiz negativo =%f",comp_horiz[d]);
         comp_horiz [d]= chg_asis[d] ;
       comp_vert[d] = 0 ; }
      else
       comp_vert  [d] = (chg_asis[d] - comp_horiz [d] ) ; }
     }
    dist_vert+=comp_vert[d] ;
    dist_horiz+=comp_horiz [d] ;
    printf("\n%i %i %f %f %f %f %f",nod_p2t[d],d,comp_horiz[d],horiz[d],comp_vert[d],vert[d],chg_asis[d]);
    //printf("\nNodoTNT %i nodo %i. CompH=%f/horiz=%f CompV=%f/vert=%f DistAsis=%f",nod_p2t[d],d,comp_horiz[d],horiz[d],comp_vert[d],vert[d],chg_asis[d]);
  }
}
printf("\nTotal: DistH=%f DistV=%f DistASIS=%f",dist_horiz,dist_vert,dist_asis) ;




fflush(stdout);
return (0);
}



showachange (int sp1, int sp2,int stg_asi,int stg_anc,int stg_des, int sisi  ) {
int a ,l,nodA,nodD;
Punktyp * pt_aln  ;



nodA= 99999;
nodD= 999999;

if ( sisi ){  // mapeo de asis
 sprintf(otherFilename, "pairs_%s_aln.tnt",bltype);
 output_file= fopen(otherFilename, "w");

 fprintf(output_file,"\n nstates 32;\nmxram 300;");
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
                 /* if (sp1== 1 && sp2 == 5 )
                       printf ("Score dock as is\n"); */
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
                     /* if (sp1== 1 && sp2 == 5 )
                       printf ("%i=%f\n",a,dist_start);  */
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
 if (dointerp){
    penalty = tot  ;
    penalty = penalty /( nucateg * 3  )  ; // (nucateg * 2 )
     }
 else{
   penalty = tot ;
   penalty = penalty /nucateg ;
   penalty /= 2.6 ; } //2.6
 penalty = penalty  * (  pen_fac  );
 }



void conf_by_categs(nuspec,nucateg){
 int a , b , c, vani, conf;
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
         vani = 0 ;
         for (c=0 ; c <  pt_sp[a].num_confs  ; c ++ ){
           conf = pt_sp[a].conflist[c];
           if (pt_conf[conf].which_class == b )
             vani ++ ;}
          printf ("%i ",vani);}
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


//voy a calcular la distancia entre Ã‘ y Fermat sobre la recta anterior.

DistF= Distanciero_3d (X_No, Y_No ,0 ,0 , 0, 0 ) ; //printf ("\n  DistF :%f \n",  DistF ) ;

//voy a calcular la distancia entre Izq y Ã‘

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
  if (dostre) make_d_stretchs_recat () ;
  if (doinvstre) make_inv_stretchs_recat () ;
  if (doshstre) make_shift_stretchs_recat() ;
  for( a = 0 ; a < STATES  ;a ++ )
   for ( b = 0 ; b < STATES  ;b ++ ){
      if (a == b ) continue ;
        if (doshift)  make_d_shifts  (a,b,nucateg) ;}
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
      //printf("\nVIOLATION OF TRIANGLE INEQUALITY");
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
         // printf("\nVIOLATION OF TRIANGLE INEQUALITY AMONG STATES %i,%i,%i, ", a,b,c );
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
    ctos_recu ++ ;
return (ctos_recu) ;
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
     fprintf(output_file,"ID=%s/Stg_%i\n",sps_list[ a].sps_name,c);
   else
   fprintf(output_file,"ID=IntNod%i/Stg_%i\n",nod_p2t[a],c);

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
     fprintf(output_file,"ID=%s/Stg_%i\n",sps_list[ a].sps_name,c);
   else
   fprintf(output_file,"ID=IntNod%i/Stg_%i\n",a,c);

    }
   }
fclose(output_file);
}


generate_tps_recat (int nuteg) {
int a,l,c,stag,min,max ;
double guer,age,ddes ;
Punktyp * pt ;
outputFilename[0] = NULL;
strcat (outputFilename,prefix);
strcat(outputFilename, "_trajectories.tps");
output_file= fopen(outputFilename, "w");


outputFilename[0] = NULL;
strcat (outputFilename,prefix);
strcat(outputFilename, "_info.txt");
sank_file= fopen(outputFilename, "w");
fprintf(sank_file,"Configuration,Species/IntNode,Aligned_Stage,Rel_Pos,Age\n");


for (a=0 ; a < nnods; a++ ) {
	 stag = 0 ;
	 for (c=0 ; c < nuteg; c++ )
	  if (mask_aln[a][c] != 0 )
	   stag++ ;
      guer = 1/ ((double)stag - 1) ;
	for (c=0 ; c < nuteg; c++ ) {
	 min = 0 ;
	 if (mask_aln[a][c] != 0){
	   min = c ; break ; }}
	  for (c= nuteg - 1 ; c > 0; c-- ) {
	  max = nuteg - 1 ;
	 if (mask_aln[a][c] != 0){
	   max = c ; break ; }}
 ddes = (max_cont[a] - min_cont[a])  / ((double)stag - 1 ) ; //min_cont y max_cont son leidos de la optimizacion de tnt. TNT lee de los terminales el promedio de age para todos los individuos de la categoria final e inicial
 stag = 0 ;
 for (c=0 ; c < nuteg; c++ ) {
 age = min_cont[a]  + (stag * ddes) ;
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
     if (c == max ){
      fprintf(output_file,"ID=%s/Stg_%i_Offset\n",sps_list[ a].sps_name,c);
      fprintf(sank_file,"%s/Stg_%i_Offset,%s,%i,%.3f,%.3f\n",sps_list[a].sps_name,c,sps_list[a].sps_name,c,(stag * guer),age);
      }
     else
      if ( c == min ){
         fprintf(output_file,"ID=%s/Stg_%i_Onset\n",sps_list[ a].sps_name,c);
         fprintf(sank_file,"%s/Stg_%i_Onset,%s,%i,%.3f,%.3f\n",sps_list[a].sps_name,c,sps_list[a].sps_name,c,(stag * guer),age); }
      else{
        fprintf(output_file,"ID=%s/Stg_%i\n",sps_list[ a].sps_name,c);
        fprintf(sank_file,"%s/Stg_%i,%s,%i,%.3f,%.3f\n",sps_list[a].sps_name,c,sps_list[a].sps_name,c,(stag * guer),age); }
    else
     if (c == max ){
      fprintf(output_file,"ID=IntNod%i/Stg_%i_Offset\n",nod_p2t[a],c);
      fprintf(sank_file,"IntNod%i/Stg_%i_Offset,%i,%i,%.3f,%.3f\n",nod_p2t[a],c,nod_p2t[a],c,(stag * guer),age);}
    else
     if ( c == min ){
      fprintf(output_file,"ID=IntNod%i/Stg_%i_Onset\n",nod_p2t[a],c);
      fprintf(sank_file,"IntNod%i/Stg_%i_Onset,%i,%i,%.3f,%.3f\n",nod_p2t[a],c,nod_p2t[a],c,(stag * guer),age);}
     else{
       fprintf(output_file,"ID=IntNod%i/Stg_%i\n",nod_p2t[a],c);
       fprintf(sank_file,"IntNod%i/Stg_%i,%i,%i,%.3f,%.3f\n",nod_p2t[a],c,nod_p2t[a],c,(stag * guer),age) ;}
 stag++ ;
 }
}


fclose(output_file);
fclose(sank_file);
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

fill_bakmtx(){
int c , i, s,n;
Sptyp * pt_sp ;
Conftyp * pt_dt, * pt_bk ;
pt_dt = datamatrix ;
pt_bk = back_mtx ;
  ///ACA TENGO QUE CORREGIR ESTOOOOOOO // // hay una fill y otra restore bakup hay q verlas


 for (s = 0 ; s < nuspecs ; s ++){
  bak_sps_list[s].num_confs  =  sps_list[s].num_confs ;
  bak_sps_list[s].sp_number =  sps_list[s].sp_number ;
  strcpy(bak_sps_list[s].sps_name,sps_list[s].sps_name);
  for (n = 0 ; n < sps_list[s].num_confs ; n ++)
  {
  c= bak_sps_list[s].conflist[n] = sps_list[s].conflist[n] ;
  pt_bk = back_mtx    ; pt_bk+=c  ;
  pt_dt = datamatrix  ; pt_dt+=c  ;
  pt_bk->age = datamatrix[c].age ;
  pt_bk->std_sp_age = pt_dt->std_sp_age ;
  pt_bk->age_aln     = pt_dt->age_aln ;
  pt_bk->sp_number   = pt_dt->sp_number ;
  pt_bk->confnumber  = pt_dt->confnumber ;

  pt_bk->nulands     = pt_dt->nulands ;
  pt_bk->which_class = pt_dt->which_class ;
  pt_bk->which_hyp_class = pt_dt->which_hyp_class ;
  pt_bk->which_str_class = pt_dt->which_str_class ;
  pt_bk->which_aln_class = pt_dt->which_aln_class ;
  strcpy(pt_bk->ind_number,pt_dt->ind_number) ;
  strcpy (pt_bk->sps_name,pt_dt->sps_name) ;
  for ( i = 0 ; i < LANDS ; i ++ ){
   pt_bk->pt[i].x = pt_dt->pt[i].x ;
   pt_bk->pt[i].y = pt_dt->pt[i].y ;
   if (DIMS == 3)
     pt_bk->pt[i].z = pt_dt->pt[i].z ; }
   }
 }






}//fill_bakmtx



int resample (int nuspecs, int nucategs, int extended){
int n, yeso, opt_asis,a,b , i, r, figura,standa,standb, cofi;
int  starposR, starpos, val, endposR, endpos;
double newscore,range ;

for (n=0 ; n < nnods ; n++){
  trans_freq [ n ] [0]  = 0  ;
  trans_freq [ n ] [1]  = 0  ;}
conf_x_categ (nuspecs,nucategs ) ;

for (i = 1 ; i < (replications + 1)  ; i ++){
  if ( dointerp ){
      //printf("\n");
     cofi = sample_datamatrix ();
     interpolate_cont(cofi,i);
     define_limits ( nucategs , nuspecs );
   //  printf("\nvuelta %i-----------------------",i );

     if (use_observed)
       sorting_confs_in_cats ( nucategs , nuspecs , cofi,1 ) ;
     else{
         cofi = CAT_INTER *  nuspecs ;
         sorting_confs_in_cats ( nucategs , nuspecs ,cofi ,1 ) ;}
     fill_consense_matrix(nuspecs,nucategs,LANDS) ;    }
   else
     fill_consense_matrix_resample(nuspecs,nucategs,i) ;
  dde_cns_mtx =nuspecs ;

 if (extended)
    build_extended_states(nuspecs, nucategs) ;
   for( a = 0 ; a < STATES  ;a ++ )
    for ( b = 0 ; b < STATES  ;b ++ ){
      if (a == b ) continue ;
         make_as_is (a,b,nucategs,STATES) ;}
  if (penalize)
    calculate_penalty (nuspecs,nucategs ) ;
 /*   printf("\nPenalty:%f",penalty); */
  fill_sankoff_costs(nuspecs,nucategs) ;
  put_best_score (nucategs) ;
  triangle_ineq () ;
  yeso=0  ;  opt_asis = 0;
  sank_downpass () ;
  sank_uppass () ;
  newscore= fill_reconstructions_new (nt) ;
  //printf("\n paso fil_recons");
  map_changes (0,i) ;
  //printf("\npaso map changes");
  range = define_d_pairings_recat ( 0, NUCATEG, i ) ;  //define inf_limit y sup_lmit_cont. El mas chico de todo el alin es 0. aca redondeo too
  catlin_reco[ i - 1] = (int) range ;
 for (n=0 ; n < nnods ; n++){
    if (easy_trans[n][0] != 0){
	 if (( easy_trans_rnd[i][n][0] > 0 ) && ( easy_trans[n][0] > 0 ) || ( easy_trans_rnd[i][n][0] < 0 ) && ( easy_trans[n][0] < 0 ))
	 trans_freq [n][0] ++;}
	if ( easy_trans[n][1] != 0){
	 if (( easy_trans_rnd[i][n][1] > 0 ) && ( easy_trans[n][1] > 0 ) || ( easy_trans_rnd[i][n][1] < 0 ) && ( easy_trans[n][1] < 0 ))
	  trans_freq [n][1] ++;}}
procrustear_trayectoria(i-1 ) ;
}
//generate_d_svg(catlin_reco[0],1,1,1) ;
for (n=0 ; n < nnods ; n++){
	trans_relf [n][0] = 100 * (double) trans_freq [n][0] / (double)replications ;
    trans_relf [n][1] = 100 * (double) trans_freq [n][1] / (double)replications ;}

restitute_datamtx ();
restitute_consense_matrix (   nuspecs,  nucategs,  LANDS  ) ;

return (1) ;
}

restitute_datamtx (){
int c , i,s;
Conftyp * pt_dt, * pt_bk ;
pt_dt = datamatrix ;
pt_bk = back_mtx ;

 for (c = 0 ; c < orig_confs ; c ++)
 {
  pt_dt->age = pt_bk->age ;
  pt_dt->std_sp_age = pt_bk->std_sp_age ;
  pt_dt->age_aln     = pt_bk->age_aln ;
  pt_dt->sp_number   = pt_bk->sp_number ;
  pt_dt->confnumber  = pt_bk->confnumber ;
   pt_dt->nulands     = pt_bk->nulands ;
  pt_dt->which_class = pt_bk->which_class ;
  pt_dt->which_hyp_class = pt_bk->which_hyp_class ;
  pt_dt->which_str_class = pt_bk->which_str_class ;
  pt_dt->which_aln_class = pt_bk->which_aln_class ;
  strcpy (pt_dt->sps_name,pt_bk->sps_name) ;
  strcpy (pt_dt->ind_number,pt_bk->ind_number) ;
  for ( i = 0 ; i < LANDS ; i ++ ){
   pt_dt->pt[i].x = pt_bk->pt[i].x ;
   pt_dt->pt[i].y = pt_bk->pt[i].y ;
   if (DIMS == 3)
     pt_dt->pt[i].z = pt_bk->pt[i].z ; }
   pt_dt ++ ; pt_bk++ ;
 }
 for (s = 0 ; s < nuspecs ;s ++){
   sps_list[s].num_confs = bak_sps_list[s].num_confs ;
   for (i = 0 ; i < bak_sps_list[s].num_confs; i++)
       sps_list[s].conflist[i] = bak_sps_list[s].conflist[i] ;}

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
int izq , der,soni,sond ;
izq= firs[ nt] ;
der = sis[izq] ;
ctos_recu = 0;
 soni = all_desc (izq);
 if (soni ==1){
  OUTGRP = izq ;
  return ;}
ctos_recu = 0 ;
 sond = all_desc (der);
 if (sond == 1){
  OUTGRP = der ;
  return ;}
 if (sond < soni ){
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
           valor =  rand() % 100 ;
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
}  //fill_consense_matrix_resample





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
remove ("asis_2pasos.tmp");
remove ("trans.tmp");



/* showachange sirve para ver el cambio entre dos nodos pueden ser terminales o nodos internos solo que tiene q ser solo con !doall */
//showachange (ances,desce,stg_asis,stg_ancH,stg_desH,1) ; // aca imprime en el archivo las configs optimizadas desde TNT como asis
if (!doal)
 scor_AS_TNT = score_by_branch (1 ) ; // uno quiere decir que usa as is
fclose (input_file) ;
generate_tps_asis () ;
calculate_disparity (NUCATEG);

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
cat_alin = generate_alignment_recat (0,WAT_CHG,-1) ;
if (doperc)
 map_changes_perc(0,0,1);


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

void define_limit_stretch  ( int cto,int nucats, int especie, int inver ) {
int lims,  j , l ;
double span ;

if (inver == 0 ){
 if (cto < 0 ){
   lims = nucats + 1  + cto ;
   span = (sps_list[especie].max_age -  sps_list[especie].min_age ) / ( lims - 1 );}
 else {
  lims = nucats  + 1 ;
  span =  ( limits[especie][nucats - cto] - sps_list[especie].min_age) / (lims - 1 ); } //  (nucats - cto) = es xq dejo ctos "sobresaliendo".  antes dividia la trayectoria en nucats+cto y tomaba para comparar nucats. Ahora elijo el span primero (nucats-cto y eso lo dividoen nucats)
  for (j = 0 ; j < lims    ; j ++ )
   limits_str  [j] = sps_list[especie].min_age  + ( span * j ) ;
} else //si es invertido
 {
  if (cto < 0 ){
   lims = nucats  + 1 ;
   span =  ( sps_list[especie].max_age - limits[especie][ -cto ]) / (lims - 1 ); }
  else{
   lims = nucats + 1 - cto ;
   span =  ( sps_list[especie].max_age - sps_list[especie].min_age) / (lims - 1 ); }
   l =  0;
   for (j = nucats  ; j > (nucats - lims  ) ; j -- ){
    limits_str  [j] = sps_list[especie].max_age  - ( span * l ) ;
    l ++ ; }
 }
}



void define_limit_db_stretch  ( int star,int nucats, int especie,int fin ) {//(i,NUCATEG,sp1,j) ; // cambio_izq,Ncateg,spamodif,cambio_der)
int lims,  j,van   ;
double span, age_star , age_end, cat_star;



if ((star > 0 ) && (fin < 0 )){ //si +  izq y - derecha
   lims = nucats + 1 - star + fin ;
   span = ( limits[especie][nucats] -  limits[especie][0]  ) /  ( lims - 1 ) ;
   //span = ( sps_list[especie].max_age -  sps_list[especie].min_age +  1  ) /  ( lims - 1 ) ;
   // span = ( sps_list[especie].max_age -  sps_list[especie].min_age   ) /  ( lims - 1 ) ; //le sumo uno xq va de 0 a 5 las categ entonces son 6.
   age_star = sps_list[especie].min_age ;
   cat_star = star; }

if ((star < 0 ) && (fin < 0 )){ //si -  izq y - por derecha
 lims = nucats + 1  + fin ;
 //lims = nucats  + 1 ;
/* span = (sps_list[especie].max_age -  limits[especie][nucats + star] ) / ( lims - 1 );*/
 /* lims = nucats + 1  + fin + star ;*/
   //span = (sps_list[especie].max_age -  limits[especie][ - star]   ) / ( lims - 1 );
   span = ( limits[especie][nucats] -  limits[especie][ - star]   ) / ( lims - 1 );
  age_star = limits[especie][ - star] ;
 cat_star = 0 ;
}

if ((star > 0 ) && (fin > 0 )) {//si +  por izq y +  derecha
lims = nucats + 1 - star  ;
span = (  limits[especie][nucats - fin ] - limits[especie][0] ) / ( lims - 1 ) ;
age_star = sps_list[especie].min_age;
cat_star = star ;
 }
if ((star < 0 ) && (fin > 0 ) ){//si -  izq y +  por derecha
lims = nucats + 1  ;
span =    ( limits [ especie ][ nucats - fin ] -  limits [ especie ][ - star ] ) / ( lims - 1 );
//span =    ( limits [ especie ][ nucats - fin ] -  limits [ especie ][ nucats + star ] ) / ( lims - 1 );
age_star =  limits [ especie ][ - star ] ;
cat_star = 0 ;
}
/// ESTOY ACA!!!!  DESPUES SEGUIR CORRIGIENDO EL RESTO DE LAS FUNCIONES
van = 0 ;
  for (j = cat_star ; j < ( cat_star + lims )  ; j ++ ){
     limits_str [j] = age_star  + ( span * van ) ;
     van++ ; }

}




int sorting_confs_in_cats_stretch (int nucats, int nusp, int nuconf, int especie, int cto, int invertido, int final ){
int  j , cual=0, k,edad, start ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_conf = datamatrix ;
pt_sp = sps_list ;

start = 0;
if (invertido == 2){
  if (cto > 0 ){
    start = cto ; }
  if (final < 0 )
    nucats += final ;

}

if ( invertido == 1 && cto > 0 ){
 start = cto ;
 }
if ( invertido == 0 && cto < 0 )
    nucats += cto ;  // si se acorta bajo el numero sino queda queda el mismo numero de categs



 //con invertido y cto negativo se deben mantener las categs.

for (j = start ;  j <  nucats     ; j ++)
  yes_str [j] = 0   ;
for (j = start ;  j <  nuconf     ; j ++)
  pt_conf [j].which_str_class = -1 ;

for (j = 0 ;  j < pt_sp [ especie ].num_confs  ; j ++)
        {
         cual = pt_sp [especie].conflist [j] ;
       /*   if (cual == pt_sp [especie].confmaxage ){  // ESTO ARREGLARLO
                pt_conf[cual].which_str_class = nucats - 1 ;
                yes_str [nucats-1] = 1 ;
                continue;}*/
          for (k = start ;  k < nucats    ; k ++)
          {
           if (timeas)
            {
             if ( k == 0  )
              {
               if ( ( pt_conf[cual].age >= limits_str[k] ) && (pt_conf[cual].age <= limits_str [k+1] ) )
                {
                  yes_str [k] ++ ;
                  pt_conf[cual].which_str_class = k ;
                 }
              }
             else
              if (( ( pt_conf[cual].age > limits_str[k] ) && (pt_conf[cual].age <= limits_str [k+1] ) ))      //|| ( cual ==pt_sp[especie].confmaxage))
              {
               yes_str [k] ++ ;
               pt_conf[cual].which_str_class = k ;
              }
            }
           else
            {
             edad = pt_conf[cual].age ;
             if (  edad  ==  k )
             {
              yes_str[k] ++ ;
              pt_conf[cual].which_str_class = k ;}
             }
          }
        }

if (!dointerp){
   for (j = start ;  j < nucats  ; j ++)
     if (yes_str [j] == 0 ){
      printf("\nStretch %i in sp %i cannot be done given the lack of data",especie, cto);
      printf("\nNo obs for cat %i (%f-%f) species %i",j,limits_str[j],limits_str[j+1],especie);
      printf("\n") ;
      return (0) ;}}


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
     if (cto > 0 ) {  // cuando el mov es positivo achico el numero de cats del modificado y comparo con un numero reducido de la referencia. Ademas empieza al final de la trayect
      cual = cto ;   start =  cto   ; finish = nucats ;  }
     else{
      cual = 0 ; start = 0 ; finish = nucats ; //cuando es negativo compara todas las categs del referencia con las del modificado excepto las mas bajas q son las que quedas afuera
        }

     for (j = start ;  j <  finish   ; j ++)
     {
      for (l = 0 ; l < nulan ; l++){
       buff_dock[0].pt[l].x = 0;  buff_dock[0].pt[l].y = 0; buff_dock[0].pt[l].z = 0 ;}
       son = 0 ;
     for (i = 0 ;  i < pt_sp[ especie_to_str ].num_confs  ; i ++)
     {
      conf =  pt_sp[ especie_to_str ].conflist[i] ;
      if ( pt_conf [conf].which_str_class == cual )
       {
          for (l = 0 ; l < nulan ; l++){
            buff_dock[0].pt[l].x  +=pt_conf[conf].pt[l].x ;
            buff_dock[0].pt[l].y  +=pt_conf[conf].pt[l].y;
            buff_dock[0].pt[l].z  +=pt_conf[conf].pt[l].z;  }
         son ++ ;
        }
      }
     for (l = 0 ; l < nulan ; l++){
         dock2[j].pt[l].x = buff_dock[0].pt[l].x / son ;
         dock2[j].pt[l].y = buff_dock[0].pt[l].y / son ;
         dock2[j].pt[l].z = buff_dock[0].pt[l].z / son ;}
     cual ++;}
    }
    else{
     if (invertido == 2 ){
      if (cto < 0 )    // cual hace referencia a cual categoria de la modificada
        start = 0   ;
      else
       start = cto ;
      if (chgend < 0 ) {
           finish = nucats + chgend   ;}
       else{
          finish = nucats ;  }
       }//cuando es positivo compara todas las categs del referencia con las del modificado excepto las mas bajas q son las que quedas afuera
       for (j = start ;  j <  finish   ; j ++)
        {
        cual = j ;
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
       }}
return(0 );
}


double score_in_docks (int nucats, int quehago, int invertido, int chgend )
 {
  Punktyp *  pt_cf1, * pt_cf2  ;
  int  j ,  pairs = 0 , start, finish;
  int a,l,c ;
  double totscore = 0 , escore = 0 ,escoreS=0, escoreE= 0  ;
Punktyp * pt ;


if (flag==999) {
outputFilename[0] = NULL;
strcat (outputFilename,prefix);
strcat(outputFilename, "_docks.tps");
output_file= fopen(outputFilename, "w");
}


 // invertido 0 = stretch, invertido=1 str inv;invertido = 2 db stretch
 // que hago es el cambio
if (invertido == 0 ){
  if (quehago > 0){
   start = 0 ; finish = nucats ; }
  else{
   start = 0 ; finish = nucats + quehago ; } }
else{
   if (invertido == 1 ){
    if (quehago >= 0){
      start = quehago   ; finish = nucats; }
     else{
      start = 0 ; finish = nucats ;} }
    else{ // doble invertido
       if (quehago > 0)
         start = quehago  ;
       else
         start = 0 ;
       if (chgend > 0 )
          finish = nucats ;
       else
         finish = nucats + chgend ;
     }
   }

       if (cost_ends){
        pt_cf1 = dock1[start].pt ;
        pt_cf2 = dock2[start].pt ;
        escoreS = pair_conf_dist ( pt_cf1 , pt_cf2 ) ;
        pt_cf1 = dock1[finish-1].pt ;
        pt_cf2 = dock2[finish-1].pt ;
        escoreE = pair_conf_dist ( pt_cf1 , pt_cf2 ) ;
        totscore = (escoreE + escoreS )/ 2 ;
      }else{
       for (j = start; j <  finish ; j++ ) {
        pt_cf1 = dock1[j].pt ;
        pt_cf2 = dock2[j].pt ;
       if ( ( pt_cf1[0].x != -10000001) && ( pt_cf2[0].x != -10000001)  ) {
        escore = pair_conf_dist ( pt_cf1 , pt_cf2 ) ;
      /*  if (flag== 2 || flag == 3   )
         printf("%i=%f\n",j,escore); */
        totscore = escore + totscore ;
        pairs++ ;}}
        totscore = totscore / pairs ;}
        /*if (flag== 2 || flag == 3 )
         printf("totscore=%f\n",totscore);*/
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
for (i = 0 ; i < catnum ; i ++)
    dock1[i].pt = (Punktyp * ) malloc (nulan * sizeof (Punktyp)) ;
dock2 = (Conftyp * ) malloc ( catnum * sizeof (Conftyp) ) ;
for (i = 0 ; i < catnum ; i ++)
   dock2[i].pt = (Punktyp * ) malloc (nulan * sizeof (Punktyp)) ;

}

int generate_alignment_recat ( int qreco,int which_cng,int resam) {
int  catlin,a , i;
double  range, ranged;

  range = define_d_pairings_recat ( qreco, NUCATEG,resam) ;  //define inf_limit y sup_lmit_cont. El mas chico de todo el alin es 0. aca redondeo too
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
  generate_d_svg(catlin,1,-1,0);
  /*generate_species_classif_recat (catlin) ;*/
 generate_age_covariates (catlin) ; // llama a TNT, optimiza y genera un tmp dondestas los cs optimizados
 generate_tps_recat (catlin) ;
 /*generate_covariate_recat (catlin) ;*/
 if (dodisparity){
   calculate_disparity (catlin) ;
calculate_chg_hetero_newborns () ;
calculate_chg_hetero_adults ();}

printf("\n--------------------------------") ;


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
     while ((strstr(buffer_tmp,"TOTAL" ) == NULL))
                i =  read_next_line ( buffer_tmp) ;
     for (a = 0 ; a < nucag ; a ++)//aca guarda las configuraciones ancestrales inferidas por TNT.
           {
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
 //fprintf(output_file,"\nwarn-;\nsil=all;\nmacro=;\nreport-; \ncls;\ntable/7;\nclb;\n");
 fprintf(output_file,"var: node_fl node_tn ;\nlog trans.tmp ;\n");
 fprintf(output_file,"loop (ntax + 1) nnodes [0]\n set node_fl $$ttag #1 ; set node_tn #1 ; sil-all; if ('node_tn'!=root) quote $node_fl 'node_tn' ; else quote 'node_tn' 'node_tn' ; end;  sil=all;stop ; ");

 fprintf(output_file,"\nlog chg_2pasos.tmp ;\nwarn-;\nlm show;\nsil-all;\n lm ;\n sil=;log/;\n quit ; ");
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
fprintf(output_file,"\nmxram 300;");
fprintf(output_file,"\nxread\n%i %i",cats  ,nuspecs);
if (DIMS == 2 )
 fprintf(output_file,"\n&[landmark 2d]");
else
  fprintf(output_file,"\n&[landmark 3d]");
 for ( i= 0 ; i < nuspecs ; i ++)
  {
   fprintf(output_file,"\n%s ",pt_sp[ i ].sps_name,i);
   //(fprintf(output_file,"\n%s_%i ",pt_sp[ i ].sps_name,i);
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

double define_d_pairings_recat (int qreco,int nucas,int resa){
int n ,nodo, d, shift, stre ;
double uncat,maxlimit,minlimit,shifti,stree ;
Sank_spcelltyp ** pt_sank ;
pt_sank = sank_mtx ;
resa = resa - 1  ;
if (resa < 0) {
 for ( n = intnods  ;  n -- ; ){
       nodo = optlist [n] ;
       if (nodo == nt){   // esto esta mal xq pueden ser mas o menos cuando es recat!!! verrrrr
         inf_limit_cont[ nodo ] = 0 ;
         sup_limit_cont[ nodo ] = nucas   ;}
       for (d = firs[nodo] ; d != - 9  ; d = sis [ d  ] ){
          if (easy_trans[d][0] == 0  && easy_trans[d][1] == 0   ){ //if (transformations[d] == 0 )
             inf_limit_cont [ d ] = inf_limit_cont [nodo];
             sup_limit_cont [ d ] = sup_limit_cont [nodo];
             continue;  }
          if ( easy_trans[d][0] == easy_trans[d][1] ){ //(transformations[d] == 1 )
             shift=  easy_trans[d][0]; // guich_map[d] ;
             shifti = (double) shift ;
             uncat = (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas ; // esto es lo qeu corrije que un cambio de una categ en una tray acortada no es lo mismo q en una cat original
             shifti = shift * uncat ;
             trans_corr [0][d] = shifti;
             inf_limit_cont [ d ] = inf_limit_cont [nodo] + shifti ;
             sup_limit_cont [ d ] = sup_limit_cont [nodo] + shifti ;
             continue; }
          if ( easy_trans[d][0] == 0  && easy_trans[d][1] != 0   ){ //(transformations[d] == 2 )
             stre=   easy_trans[d][1]; //guich_map[d] ;
             stree = (double) stre ;
             if (stree < 0 ){
               uncat = (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas ;
               stree = stree * uncat ;}
             else
              stree = ( (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas )  * stree ;
              //stree = ( (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / (nucas - stree) ) * stree ;
             trans_corr [0][d] = stree;
             inf_limit_cont [ d ] = inf_limit_cont [nodo] ;
             sup_limit_cont [ d ] = sup_limit_cont [nodo] + stree ;
             continue ;
             }
          if ( easy_trans[d][0] != 0  && easy_trans[d][1] == 0   ){ //(transformations[d] == 3 )
             stre= easy_trans[d][0] ; // guich_map[d]
             stree = (double) stre ;
             if (stree > 0 ){
               uncat = (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas ;
               stree = stree * uncat ;}
             else
               stree = ( (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas  ) * stree ;
             //     stree = ( (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / (nucas + stree) ) * stree ;
             trans_corr [0][d] = stree ;
             inf_limit_cont [ d ] = inf_limit_cont [nodo] + stree ;
             sup_limit_cont [ d ] = sup_limit_cont [nodo] ;
             continue; }
           if ( easy_trans[d][0] != 0  && easy_trans[d][1] != 0   ){ // transformations[d] == 4 )
             shift=  easy_trans[d][0] ; //guich_map[ d ] ;
             stre =  easy_trans[d][1]  ; //guich_map [d + MAXNODES] ;
             stree = (double) stre ;
             shifti = (double) shift ;
             if (shifti > 0 ){
               uncat = (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas ;
               shifti = shifti * uncat ;}
             else
              shifti = ( (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas  ) * shifti ;
             if (stree < 0 ){
               uncat = (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas ;
               stree = stree * uncat ;}
             else
               stree = ( (sup_limit_cont[ nodo ] - inf_limit_cont [ nodo ]) / nucas  ) * stree ;
             trans_corr [0][d] = shifti ;
             trans_corr [1][d] = stree ;
             inf_limit_cont [ d ] = inf_limit_cont [nodo] + shifti ;
             sup_limit_cont [ d ] = sup_limit_cont [nodo] + stree ;
             continue; }
           }
         }
 round_aln_limits (-1) ;
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
 }
 else
 {
 for ( n = intnods  ;  n -- ; ){
       nodo = optlist [n] ;
       if (nodo == nt){   // esto esta mal xq pueden ser mas o menos cuando es recat!!! verrrrr
         inf_limit_resa[ resa ][nodo] = 0 ;
         sup_limit_resa[ resa ][nodo] = nucas   ;}
       for (d = firs[nodo] ; d != - 9  ; d = sis [ d  ] ){
          if (easy_trans_rnd[resa][d][0] == 0  && easy_trans_rnd[resa][d][1] == 0   ){ //if (transformations[d] == 0 )
             inf_limit_resa [resa] [ d ] = inf_limit_resa [resa] [ nodo ];
             sup_limit_resa [resa] [ d ] = sup_limit_resa [resa] [ nodo ];
             continue;  }
          if ( easy_trans_rnd[resa][d][0] == easy_trans_rnd[resa][d][1] ){ //(transformations[d] == 1 )
             shift=  easy_trans_rnd[resa][d][0]; // guich_map[d] ;
             shifti = (double) shift ;
             uncat = (sup_limit_resa[resa][nodo] - inf_limit_resa[resa][nodo]) / nucas ; // esto es lo qeu corrije que un cambio de una categ en una tray acortada no es lo mismo q en una cat original
             shifti = shift * uncat ;
             trans_corr [0][d] = shifti;
             inf_limit_resa [resa] [ d ] = inf_limit_resa[resa] [nodo] + shifti ;
             sup_limit_resa [resa] [ d ] = sup_limit_resa[resa] [nodo] + shifti ;
             continue; }
          if ( easy_trans_rnd[resa][d][0] == 0  && easy_trans_rnd[resa][d][1] != 0   ){ //(transformations[d] == 2 )
             stre=   easy_trans_rnd[resa][d][1]; //guich_map[d] ;
             stree = (double) stre ;
             if (stree < 0 ){
               uncat = (sup_limit_resa[resa][ nodo ] - inf_limit_resa [resa][ nodo ]) / nucas ;
               stree = stree * uncat ;}
             else
              stree = ( (sup_limit_resa[resa][ nodo ] - inf_limit_resa [resa][ nodo ]) / nucas )  * stree ;
              //stree = ( (sup_limit_resa[ nodo ] - inf_limit_resa [ nodo ]) / (nucas - stree) ) * stree ;
             trans_corr [0][d] = stree;
             inf_limit_resa [resa] [ d ] = inf_limit_resa [resa][nodo] ;
             sup_limit_resa [resa] [ d ] = sup_limit_resa [resa][nodo] + stree ;
             continue ;
             }
          if ( easy_trans_rnd[resa][d][0] != 0  && easy_trans_rnd[resa][d][1] == 0   ){ //(transformations[d] == 3 )
             stre= easy_trans_rnd[resa][d][0] ; // guich_map[d]
             stree = (double) stre ;
             if (stree > 0 ){
               uncat = (sup_limit_resa[resa][ nodo ] - inf_limit_resa [resa][ nodo ]) / nucas ;
               stree = stree * uncat ;}
             else
               stree = ( (sup_limit_resa[resa][ nodo ] - inf_limit_resa[resa] [ nodo ]) / nucas  ) * stree ;
             //     stree = ( (sup_limit_resa[ nodo ] - inf_limit_resa [ nodo ]) / (nucas + stree) ) * stree ;
             trans_corr [0][d] = stree ;
             inf_limit_resa [resa] [ d ] = inf_limit_resa[resa] [nodo] + stree ;
             sup_limit_resa [resa] [ d ] = sup_limit_resa [resa][nodo] ;
             continue; }
           if ( easy_trans_rnd[resa][d][0] != 0  && easy_trans_rnd[resa][d][1] != 0   ){ // transformations[d] == 4 )
             shift=  easy_trans_rnd[resa][d][0] ; //guich_map[ d ] ;
             stre =  easy_trans_rnd[resa][d][1]  ; //guich_map [d + MAXNODES] ;
             stree = (double) stre ;
             shifti = (double) shift ;
             if (shifti > 0 ){
               uncat = (sup_limit_resa[resa][ nodo ] - inf_limit_resa[resa] [ nodo ]) / nucas ;
               shifti = shifti * uncat ;}
             else
              shifti = ( (sup_limit_resa[resa][ nodo ] - inf_limit_resa [resa][ nodo ]) / nucas  ) * shifti ;
             if (stree < 0 ){
               uncat = (sup_limit_resa[resa][ nodo ] - inf_limit_resa[resa] [ nodo ]) / nucas ;
               stree = stree * uncat ;}
             else
               stree = ( (sup_limit_resa[resa][ nodo ] - inf_limit_resa[resa] [ nodo ]) / nucas  ) * stree ;
             trans_corr [0][d] = shifti ;
             trans_corr [1][d] = stree ;
             inf_limit_resa [resa] [ d ] = inf_limit_resa[resa] [nodo] + shifti ;
             sup_limit_resa [resa] [ d ] = sup_limit_resa [resa][nodo] + stree ;
             continue; }
           }
         }
 round_aln_limits (resa ) ;
 minlimit =9000 ; maxlimit = -3000 ;
 for ( n = 0 ;  n < nnods ;n ++ ){
        if (inf_limit_resa[resa] [n] < minlimit)
         minlimit = inf_limit_resa[resa][n];
        if (sup_limit_resa [resa][n] > maxlimit)
         maxlimit = sup_limit_resa[resa][n];}

   maxlimit = maxlimit - minlimit ;
  for ( n = 0 ;  n < nnods ;n ++ ){
         inf_limit_resa[resa][n] =  inf_limit_resa[resa][n] - minlimit ;
         sup_limit_resa[resa][n] =  sup_limit_resa[resa][n] - minlimit ;
           }
}



 return (maxlimit) ;
}

void round_aln_limits (int resa) {
    int n , pis, caca ;

  if (resa < 0 ){
  for ( n = 0 ;  n < nnods ;n ++ ){
     if (inf_limit_cont[n] >= 0 )
      inf_limit_cont[n] = inf_limit_cont[n] + 0.5  ;
     else
       inf_limit_cont[n] = inf_limit_cont[n] - 0.5  ;
     if (sup_limit_cont[n] >= 0 )
      sup_limit_cont[n] = sup_limit_cont[n] + 0.5  ;
     else
       sup_limit_cont[n] = sup_limit_cont[n] - 0.5  ;
     caca = (int) inf_limit_cont[n] ;
     pis =  (int) sup_limit_cont[n] ;
     inf_limit_cont[n] = caca ;
     sup_limit_cont[n]=  pis  ; }
  }else{
      for ( n = 0 ;  n < nnods ;n ++ ){
     if (inf_limit_resa[resa][n] >= 0 )
      inf_limit_resa[resa][n] = inf_limit_resa[resa][n] + 0.5  ;
     else
       inf_limit_resa[resa][n] = inf_limit_resa[resa][n] - 0.5  ;
     if (sup_limit_resa[resa][n] >= 0 )
      sup_limit_resa[resa][n] = sup_limit_resa[resa][n] + 0.5  ;
     else
       sup_limit_resa[resa][n] = sup_limit_resa[resa][n] - 0.5  ;
     caca = (int) inf_limit_resa[resa][n] ;
     pis =  (int) sup_limit_resa[resa][n] ;
     inf_limit_resa [resa][n] = caca ;
     sup_limit_resa [resa][n] =  pis  ; }
  }
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
     min_cont [ nod_t2p[a] ] = min ; max_cont [ nod_t2p[a] ] = max ; }
   fclose (input_file)    ;
   remove ("cont.tmp");
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
 remove ("ages.tmp");
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


void generate_d_svg (int catl,int iscont,int vta,int resa) {
int s,sy,x,fy,a,r,i,j, namelen, maxnamelen= -10000, starlin,finlin, dde,linsep,total,separs,ferencia ;
int *pt_rnd, *pt_eas ;
Sptyp * pt_sp ;
double opa, infdo, supdo,endY,opa_step,sx,fx,ssx,ffx,lue,x1,x2,x3,x4,minimo , maximo;
char nombre[50], numero[100] ;
nombre [0] = NULL;
pt_sp = sps_list ;

strcat (nombre,prefix);
if ( vta < 0)
 {strcat (nombre,"_traj.svg");
 svg_file= fopen(nombre, "w");}
else
 {
   itoa(vta,numero,10);
   strcat (nombre,numero);
   strcat (nombre,"_traj.svg");
   svg_file= fopen(nombre, "w");}


 for (s= 0 ; s < nuspecs; s ++){
     namelen = strlen (pt_sp[s].sps_name) ;
     if ( namelen > maxnamelen )
         maxnamelen = namelen ;}

if (maxnamelen < 5  ) // para q entren los nodos internos
     maxnamelen  = 5 ;
 starlin = (maxnamelen  * 20 )  ;
 finlin = 2000 ; //1300



 total = finlin - starlin ;
 linsep = total / catl ;
 endY = (50 * nnods) + 300  ;
 dde = 80 ;

opa_step= 1 / ( (double) replications + 1)  ;

sx = 9999 ;

if (resa){
for (s = 0 ; s < nnods ; s ++){
 for (r = 0 ; r < replications ; r ++)
    if (inf_limit_resa[r][s] < sx )
      sx = inf_limit_resa[r][s] ;}

if (sx < 0 ){
for (s = 0 ; s < nnods ; s ++){
   inf_limit_cont[s] -= (double) sx ;
   sup_limit_cont[s] -= (double) sx ;
   for (r = 0 ; r < replications ; r ++){
    inf_limit_resa[r][s] -= sx ;
    sup_limit_resa[r][s] -= sx ;}
    }
 }

for (s = 0 ; s < nnods ; s ++){
 for (r = 0 ; r < replications ; r ++){
   if ( sup_limit_resa[r][s] > catl)
    catl = sup_limit_resa[r][s] ; }}
}


minimo = 99999 ;
maximo = -9999 ;
for (s = 0 ; s < nnods ; s ++){
   if (inf_limit_cont[s] < minimo )
     minimo = inf_limit_cont[s] ; }
for (s = 0 ; s < nnods ; s ++){
   if (sup_limit_cont[s] > maximo )
    maximo = sup_limit_cont[s] ; }


for (s = 0 ; s < nnods ; s ++){
 for (r = 0 ; r < replications ; r ++){
   pt_rnd = &easy_trans_rnd[r][s][0] ; pt_eas =& easy_trans[s][0] ;
   if (*pt_rnd > 0 || *pt_rnd > *pt_eas )
     continue ;
   else
    if ( (inf_limit_cont[s] - (*pt_rnd - *pt_eas )) < minimo)
     ferencia =  inf_limit_cont[s] - ( *pt_rnd - *pt_eas ); }}





if (resa)
 do_errors(catl) ;

 fprintf(svg_file,"<svg width=\"5001\" height=\"%f\" xmlns=\"http://www.w3.org/2000/svg\" >",endY);
 for (s= 0 ; s < nnods; s ++){
        if (s < nuspecs)
          fprintf(svg_file,"\n<text x= \"5\" y=\"%i\" fill=\"black\"  font-size=\"30\" alignment-baseline=\"middle\"  font-style = \"italic\"   > %s   </text>",dde,pt_sp[s].sps_name );
        else
         fprintf(svg_file,"\n<text x= \"5\" y=\"%i\" fill=\"black\"  font-size=\"30\" alignment-baseline=\"middle\"  font-style = \"italic\"   > Node %i   </text>",dde,nod_p2t[s] );

       fprintf(svg_file,"\n<line x1 = \"%f\" y1 = \"%i\" x2 = \"%f\" y2 = \"%i\" stroke = \"black\" stroke-width = \"6\"/>",(inf_limit_cont[s] * linsep + starlin),dde,(sup_limit_cont[s] * linsep + starlin),dde,opa_step);
       fprintf(svg_file,"\n<line x1 = \"%f\" y1 = \"%i\" x2 = \"%f\" y2 = \"%i\" stroke = \"black\" stroke-width = \"20\"/>",((inf_limit_cont[s] * linsep + starlin)-20),dde,((inf_limit_cont[s] * linsep + starlin)+20),dde,opa_step);
       fprintf(svg_file,"\n<line x1 = \"%f\" y1 = \"%i\" x2 = \"%f\" y2 = \"%i\" stroke = \"black\" stroke-width = \"20\"/>",((sup_limit_cont[s] * linsep + starlin)-20),dde,((sup_limit_cont[s] * linsep + starlin)+20),dde,opa_step);
       fprintf(svg_file,"\n<line x1 = \"%f\" y1 = \"%i\" x2 = \"%f\" y2 = \"%i\" stroke = \"black\" stroke-width = \"20\"/>",((sup_limit_cont[s] * linsep + starlin)-20),dde,((sup_limit_cont[s] * linsep + starlin)+20),dde,opa_step);
       if (resa){
            for (r=0; r < replications; r++){
			 pt_rnd = &easy_trans_rnd[r][s][0] ; pt_eas =&easy_trans[s][0] ;
			 if (*pt_rnd > *pt_eas)
			    sx = (inf_limit_cont[s] + (*pt_rnd - *pt_eas)   ) * linsep + starlin ;
			 else
			    sx = (inf_limit_cont[s] - (*pt_eas - *pt_rnd)   ) * linsep + starlin ;
            pt_rnd = &easy_trans_rnd[r][s][1] ; pt_eas = &easy_trans[s][1] ;
		   	if (*pt_rnd > *pt_eas)
		   	  fx = (sup_limit_cont[s] + (*pt_rnd - *pt_eas)   ) * linsep + starlin ;
		   	else
		   	  fx = (sup_limit_cont[s] - (*pt_eas - *pt_rnd)   ) * linsep + starlin ;
          fprintf(svg_file,"\n<line x1 = \"%f\" y1 = \"%i\" x2 = \"%f\" y2 = \"%i\" stroke = \"black\" opacity =\"%f\" stroke-width = \"16\"/>",(inf_limit_cont[s] * linsep + starlin),dde,sx,dde,opa_step);
          fprintf(svg_file,"\n<line x1 = \"%f\" y1 = \"%i\" x2 = \"%f\" y2 = \"%i\" stroke = \"black\" opacity =\"%f\" stroke-width = \"16\"/>",(sup_limit_cont[s] * linsep + starlin),dde,fx,dde,opa_step);}
       }
      dde = dde + 45 ;
      }
      if(resa){
      opa = 0.2 ;
	  dde = dde + 20  ;
      for ( i = 0 ; i < 5 ; i ++){
        fprintf(svg_file,"\n<text x= \"%i\" y=\"%i\" fill=\"black\"  font-size=\"30\" alignment-baseline=\"middle\"  font-style = \"italic\"   > Frequency  %.1f  </text>",(400 * i ), dde,opa );
        fprintf(svg_file,"\n<line x1 = \"%i\" y1 = \"%i\" x2 = \"%i\" y2 = \"%i\" stroke = \"black\" opacity =\"%f\" stroke-width = \"24\"/>",(400 * i + 200 ),dde-7,(400 * i + 300 ) + 60 ,dde-7,opa);
        opa+= 0.2 ; }}

x = starlin ;
j= 0 ;
sy = 40 ;
fy = 70 + 45 * ((2 * nuspecs) -1);
for (a = 0 ; a < catl ; a ++ ){
	 fprintf(svg_file,"\n<line x1 = \"%i\" y1 = \"%i\" x2 = \"%i\" y2 = \"%i\" stroke-dasharray=\"15,5\" stroke = \"black\" stroke-width = \"2\"/>",x,sy,x,fy);
     if ((a >= minimo) && (a < maximo) ){
      fprintf(svg_file,"\n<text x= \"%i\" y = \"%i\" font-size=\"30\" text-anchor=\"middle\" >  %i </text> ", x + linsep/2,sy,j);
      j++;}
    x = x + linsep ;
       }
 fprintf(svg_file,"\n<line x1 = \"%i\" y1 = \"%i\" x2 = \"%i\" y2 = \"%i\" stroke-dasharray=\"15,5\" stroke = \"black\" stroke-width = \"3\"/>",x,sy,x,fy);
fprintf(svg_file,"\n</svg>");

fclose (svg_file) ;

}




void do_errors (int tegs) {
int sch,plac,izq,der,s,j,r,vamos=0  ;
double lue;


lue = (double) replications * 0.95 ;


 for (s= 0 ; s < nnods ; s++){
  for (j=0 ; j < (tegs*2); j++){
	 ctos_ahi [0][j] = 0 ; ctos_ahi [1][j] = 0 ; }
  for (r= 0 ;  r < replications ; r++){
	if ( easy_trans_rnd[r][s][0] == easy_trans[s][0])
	  ctos_ahi [0][0] ++ ;
	else
	 if ( easy_trans_rnd[r][s][0] < easy_trans[s][0]){
		plac =  easy_trans[s][0] - easy_trans_rnd[r][s][0] ;
	    ctos_ahi[0][plac] ++ ;}
	else{
	    plac =   easy_trans_rnd[r][s][0] -  easy_trans[s][0]  ;
	    ctos_ahi[1][plac] ++ ;}
   }
   if ( ctos_ahi[0][0] >= lue){
     error[s][0][0] = 0 ; error[s][0][1] = 0 ;}
   else{
	 izq = 1 ; der  = 1;
	 vamos = ctos_ahi[0][0] ;
	 sch = 0 ;
     while (1){
	   if ((ctos_ahi[0][izq] == 0) && (ctos_ahi[1][der]== 0 ) ) {
	    izq++ ; der ++ ; sch++ ;   continue ; }
	   if (ctos_ahi[0][izq] > ctos_ahi[1][der]){
	    vamos = vamos + ctos_ahi[0][izq] ;
	    der = der - sch ; sch =0 ;
	    if (vamos >= lue ){
	      der = der - 1 ;
	      error[s][0][0] = izq ; error[s][0][1] = der ;
	     break ;
	      }
	     izq ++ ;
	     continue ;
	   }
	   else{
	    vamos = vamos + ctos_ahi[1][der] ;
	    izq = izq - sch ; sch =0 ;
	    if (vamos >= lue){
		 izq= izq - 1  ;
	     error[s][0][0] = izq ; error[s][0][1] = der ;
		 break ; }
	    }
	   der++ ;
	   continue ;
	}
  }
}
vamos = 0 ;
for (s= 0 ; s < nnods ; s++){
  for (j=0 ; j < (tegs*2); j++){
	 ctos_ahi [0][j] = 0 ; ctos_ahi [1][j] = 0 ; }
  for (r= 0 ;  r < replications ; r++){
	if ( easy_trans_rnd[r][s][1] == easy_trans[s][1] )
	  ctos_ahi [0][0] ++ ;
	else
	 if ( easy_trans_rnd[r][s][1] < easy_trans[s][1]){
		plac =  easy_trans[s][1]- easy_trans_rnd[r][s][1] ;
	    ctos_ahi[0][plac] ++ ;}
	else{
	    plac =  easy_trans_rnd[r][s][1] - easy_trans[s][1]  ;
	    ctos_ahi[1][plac] ++ ;}
   }
   if ( ctos_ahi[0][0] >= lue){
     error[s][1][0] = 0 ; error[s][1][1] = 0 ;}
   else{
	 izq = 1 ; der  = 1;
	 vamos = ctos_ahi[0][0] ;
	 sch = 0 ;
     while (1){
	   if ((ctos_ahi[0][izq] == 0) && (ctos_ahi[1][der]== 0 ) ) {
	    izq++ ; der ++ ; sch++ ;   continue ; }
	   if (ctos_ahi[0][izq] > ctos_ahi[1][der]){
	    vamos = vamos + ctos_ahi[0][izq] ;
	    der = der - sch ; sch =0 ;
	    if (vamos >= lue ){
	      der = der - 1 ;
	      error[s][1][0] = izq ; error[s][1][1] = der ;
	     break ;
	      }
	     izq ++ ;
	     continue ;
	   }
	   else{
	    vamos = vamos + ctos_ahi[1][der] ;
	    izq = izq - sch ; sch =0 ;
	    if (vamos >= lue){
		 izq= izq - 1  ;
	     error[s][1][0] = izq ; error[s][1][1] = der ;
		 break ; }
	    }
	   der++ ;
	   continue ;
	}
  }
}
}//do_errors



procrustear_trayectoria (int vta  ){
int i,n, best_dist, tancia,a, bes_mov,min ;

bak_trays (vta) ;
best_dist= calculate_dist_tray (vta) ;
bes_mov = 0 ;
for ( i = - CAT_INTER_AVG ; i < CAT_INTER_AVG  ; i++){
  if ( i == 0 ) continue ;
  for (n = 0 ; n < nnods ; n++){
    sup_limit_resa[vta][n]+= i ;
    inf_limit_resa[vta][n]+= i ;}
    tancia = calculate_dist_tray (vta) ;
  if ( tancia < best_dist  ){
    best_dist = tancia ;
    bes_mov = i ;
    }
  restor_trays(vta); }
if ( bes_mov != 0 )
 for (n = 0 ; n < nnods ; n++){
    sup_limit_resa[vta][n]+= bes_mov ;
    inf_limit_resa[vta][n]+= bes_mov ;}

}

bak_trays (int vta){
int n ;
for (n = 0 ; n < nnods ; n++){
     sup_limit_back[n] = sup_limit_resa[vta][n] ;
     inf_limit_back[n] = inf_limit_resa[vta][n] ;}
}

restor_trays (int vta){
int n ;
for (n = 0 ; n < nnods ; n++){
     sup_limit_resa[vta][n] = sup_limit_back[n] ;
     inf_limit_resa[vta][n] = inf_limit_back[n] ; }
}


calculate_dist_tray (int vta ) {
int n,dista=0  ;
for (n = 0 ; n < nnods ; n++){
     if (sup_limit_resa[vta][n] >= sup_limit_cont[n] )
      dista += sup_limit_resa[vta][n] - sup_limit_cont[n] ;
     else
      dista += sup_limit_cont[n] - sup_limit_resa[vta][n] ;
     if (inf_limit_resa[vta][n] >= inf_limit_cont[n] )
       dista += inf_limit_resa[vta][n] - inf_limit_cont[n] ;
     else
      dista += inf_limit_cont[n] - inf_limit_resa[vta][n] ;
     }
return(dista);
}


int procargs ( int nargs , char ** arg )
{
    int i ;
    char * cp ;
    int  case_d=0,  case_c =0, case_t = 0, case_i = 0 ;
    char age [5] ;
    //Globals:
    doskfile= 0; doasisfiles= 0; do_classif= 0 ; do_covfile=0 ; do_resample = 0 ;  maxstages= 0; pen_fac = 0 ; pen_ext = 1 ,outusrname ;
    dosvg = 1 ;  dospeclist = 0 ; do_deca= 0 ;dodisparity = 0 , dointerp = 1, dogapping = 0  ; doperc =  1 ; istps =  1 ;
    if ( nargs == 1 ) {
        giveme_help (  ) ;
        return( 0 ) ; }
    for ( i = 1 ; i < nargs ; ++ i ) {
        cp = arg [ i ] ;
        if ( * cp  != '-' ) {
            fprintf ( stderr , "\nWrong argument: %s\n" , arg [ i ] ) ;
            exit ( 0 ) ; }
        switch ( * ++ cp ) {
            case 'i':  cp = arg [++i] ;
               if (i >= nargs){
                 printf ("\nError. No input file defined" ) ;
                return (0); }
               strcpy (inputFilename,cp)  ; case_i = 1 ;
               istps = -1 ;
               if (strstr(inputFilename,".tps")){
                 istps = 1 ;
               }
               if (strstr(inputFilename,".txt")){
                 istps = 0 ;
               }
               if (istps == -1){
                printf ("\nError. \" Input file \"%s\" should have either tps or txt extension",inputFilename ) ;
                return (0); }
               if (istps == 0 ) {
                  cp = arg [++i] ;
                  if (i == nargs || * cp == '-' ){
                    printf("\nError while reading arguments. If data is in txt format you should indicate the number of landmarks and dimensions (2-3) after the file name ");
                          return (0);}
                  LANDS = atoi ( cp ) ;
                  cp = arg [++i] ;
                  if (i == nargs || * cp == '-' ){
                   printf("\nError while reading arguments. If data is in txt format you should indicate the number of landmarks and dimensions (2-3) after the file name");
                          return (0);}
                  DIMS = atoi ( cp ) ;}
              if (( input_file = fopen (inputFilename,"rb") )== NULL){
                  printf ("\nError. \" Input file \"%s\" not found",inputFilename ) ;
                  return (0); }
               break ;


            case 'r':   do_resample = 1 ;
                   cp = arg [++i] ;
                   replications = atoi ( cp ) ;   break ; /*resampling*/ /* falta testeo q sean menos de 1000  o alocar resampling despues de leer esto*/
            case 't':  cp = arg [++i] ;
              if (i >= nargs){
                 printf ("\nError. No tree file defined" ) ;
                return (0); }
              strcpy (treeFilename,cp)  ; case_t = 1   ; break ;
            case 'k': doskfile = 1 ;      break ;   /* generate sankoff matrix with costs */

            case 'ñ': old_mj = 1 ;      break ;   /* generate sankoff matrix with costs */

            case 'o': doasisfiles = 0 ;   pen_fac = 10000 ;  break ;       /* infer ancestral ontogenetic trajectories in the original frame of comparsion */
            case 'j': do_covfile = 1 ;      break ;       /*generate covariates and  for morphoJ*/
            case 'y': do_deca = 1 ;      break ;       /*give decay support values*/
            case 's': do_classif = 1 ; break ;     /*generate classifiers for morphoJ*/
           // case 'x': pen_ext = 0 ; break ;     /* assign a penalty independent of the number of stages implied in t he change */
            //case 'n': doperc = 1 ;  break ;     /* give changes as percetanges */
            case 'p':  cp = arg [++i] ;
                   if (i == nargs || * cp == '-' ){
			           printf("\nError while reading arguments. Give a penalty factor (0-5) ");
                   return (0);}
                   pen_fac = atoi ( cp ) ;
                   pen_fac = atoi ( cp ) ;
                   if (pen_fac < 0 || pen_fac > 5 ){
                     printf("\nError while reading arguments. Penalty factor out of scope (0-5)");
                     return (0); }
                    break ;
           /* case 'x':  cp = arg [++i] ;
                   FXDPTS = atoi ( cp ) ;
                   if (FXDPTS < 0 || FXDPTS > 15 ){
                     printf("\nError while reading arguments. fxdpoints");
                     return (0); }
                    break ;
            case 'w': dowindmax = 1 ;  break ;*/
            case 'c': blue_red = 0 ; break ;
            case 'z': cost_ends = 1 ;break  ;
            //case 'l':  dospeclist = 1 ; break ; /* Make a txt file listing specimens included in each stage for all the species */
            case 'g': dogapping = 1 ;
                 cp = arg [++i] ;
                   gap_fac = atoi ( cp ) ;
                   if (gap_fac < 0 || pen_fac > 5 ){
                     printf("\nError while reading arguments. Gapping factor out of scope (0-5)");
                     return (0); }
                    break ;
            case 'b': use_observed = 0 ;  break;  /* when interpolating exclude observed shapes */
            case 'm': color_tree = 0 ; break ;

            //case 'e': dointerp = 0 ; break ;
            case 'd':  dodisparity =  0  ;
                 cp = arg [++i] ;
                 if (i == nargs || * cp == '-' ){
                     printf("\nError while reading arguments. Indicate if disparity is calculated as variance of diatances (-d var) or as average pairwise distances (-d pair)");
                          return (0);}
                 strcpy(age,cp);
                 if (!strcmp (age,"var")){
                    dispar_var = 1 ;
                    break ; }
                  else
                    if (!strcmp (age,"pair")){
                      dispar_var = 0 ;
                      break ;}
                    else{
                     printf("\nError while reading arguments. Indicate if disparity is calculated as variance of diatances (-d var) or as average pairwise distances (-d pair)");
                          return (0);}

            case 'u':  outusrname= 1 ;
                       cp=arg[++i];
                       if (i == nargs || * cp == '-' ){
                          printf("\nError while reading arguments. No prefix for output files  (-u myprefix) ");
                          return (0);}
                        strcpy(prefix,cp);
                        break; //define a prefix for output files
              }

    }
    if (!case_i){
        printf("\nError while reading arguments. Indicate input file (-i \"myinputfile.tps\") ");
        return (0); }
    if (!case_t){
        printf("\nError while reading arguments. Indicate tree file (-t \"mytrefile.tre\")");
        return (0); }
   /* if (!case_d && !case_c){
       printf("\nError while reading arguments. Indicate whether individuals are sorted ");
      printf("\nin aprori defined stages (-a pre ), or age is given as a continuos variable (-a cont)");
      fflush(stdout);
      return (0); }*/

    return (1);
}

void giveme_help (  ) {


printf("\n  ----------------------------------------------------------------------- ");
printf("\n |                         * SPASOS v. alpha *                           |");
printf("\n |      Software for the Phylogenetic Analysis of Shape Ontogenies       |");
printf("\n |                        Author: Santiago A. Catalano                   |");
printf("\n  ----------------------------------------------------------------------- ");
printf("\n\n\n" ) ;
printf("\n* References: ");
printf("\n     - Catalano SA, MF Vera Candioti, V Segura. (2019). PASOS: a method for   ");
printf("\n       the Phylogenetic Analysis of Shape Ontogenies.  Cladistics. 35: 671-687.\n   ");
printf("\n     - Catalano SA, Segura VA, Vera Candioti MF. SPASOS v.1.0: a program      ");
printf("\n        for the inference of ancestral shape ontogenies. Submitted. ");



/*
printf("\n  ------------------------------------------------------------------- ");
printf("\n | Reference: Catalano SA, Segura VA, Vera Candioti MF (In press)    |");
printf("\n |            PASOS:a method for the Phylogenetic Analysis of        |");
printf("\n |            Shape Ontogenies. Cladistics.                          |");
printf("\n  ------------------------------------------------------------------- ");
*/


printf("\n\n* Mandatory arguments");
printf("\n\n -i \"myinputfile\"  Input data file ") ;
printf("\n       Input files can be in \"tps\" or \"txt\" format, with the corresponding extension. If the data is in \"txt\" format");
printf("\n       the number of landmarks and dimensions \(2-3\) should follow the file name. If the file is not in the same folder than");
printf("\n       SPASOS, give the full path.");
printf("\n\n -t \"mytreefile.tre\"   Input tree file ");
printf("\n\n* Optional arguments");
printf("\n\n -c     Color tree branches with violet as intermediate color (Black as default)");
printf("\n\n -m     Color tree branches according to changes in Onsets (changes in Offsets as default)");
//printf("\n\n -n     Show changes as number of stages (Default as percentange of the trajectory total span)");
//printf("\n\n -l     Make a txt file listing specimens included in each stage for all the species ");
printf("\n\n -o     Infer ancestral ontogenetic trajectories in the original frame of comparison  ");
printf("\n          i.e. force no change in developmental timing in all branches");
printf("\n\n -p   N Define a penalty factor (0 no penalty, 1 lowest, 5 highest).   Default= 0 ");
printf("\n\n -r   N Perform resampling (N replicates)");
//printf("\n\n -e  Do not use interpolating function to complete the ontogenetic trajectories ");
printf("\n\n -u  \"myprefix\" Give a prefix for output files");
//printf("\n\n -x     Assign a penalty equal for all changes in developmental timing irrespective of the number of stages implied ");
//printf("\n        in the change ");
printf("\n\n -y     Calculate decay support values");
//printf("\n\n -d  pair / var. Calculate morphological disparity along the ontogeny. The disparity can be calcuated as the average");
//printf("\n       pairwise distance between species (\"pair\") or as the variance of distance between each species and  ");
//printf("\n       the average shape for each stage (\"var\")");
//printf("\n\n -j     Generate classifiers for morphoJ ") ;
//printf("\n\n -k  Generate a file with the sankoff matrix in TNT format calculated in PASOS ");
}


int process_datafile(){
int yeso,h, especimens ;

if (istps){
 yeso = define_dimensions ();
 if (!yeso){
  printf ("Problems while reading tps file") ;
  fflush(stdout);
  return(0);}}
 else
 {
  yeso = define_dimensions_mj ();
  if (!yeso){
  printf ("Problems while reading morphoJ file") ;
  fflush(stdout);
  return(0);}}

fclose (input_file) ;
input_file = fopen (inputFilename,"rb") ;
if (DIMS < 2 ){
   printf ("Error, argument 3 (dimensions) can only take two values (2-3)") ;
   fflush(stdout); return(0); }

if (  dointerp  )
  especimens = CONFS + ( MAXSP_INTERP * CAT_INTER ) ; // MAXSP_INTERP * 100 )
 else
  especimens = CONFS ;

datamatrix = (Conftyp *) malloc ( especimens * sizeof(Conftyp) ) ;

for (h=0; h < especimens ; h++ ){
   datamatrix[h].pt =  (Punktyp *) malloc ( LANDS *   sizeof(Punktyp)) ;
   datamatrix[h].sps_name[0]='\0' ;}
back_mtx   = (Conftyp *) malloc ( especimens * sizeof(Conftyp) ) ;
for (h=0; h < especimens ; h++ ){
   back_mtx[h].pt =  (Punktyp *) malloc ( LANDS *   sizeof(Punktyp)) ;
   back_mtx[h].sps_name[0]='\0' ;}

if (istps){
  if (! (read_data()))
     return(0);
  }
  else{
    if(!(read_data_mj()))
      return(0); }

if (!timeas )
 if (!check_cats())
   return(0) ;
return (1) ;
}


int define_dimensions_mj (){
int ctas=0 ;
char   bafer [5000] ;
while (read_next_line(bafer) )
        ctas ++ ;
CONFS = ctas - 1 ;
return (1);
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
  alloc_consense_disparity( )  ;
  buff_dock = (Conftyp *) malloc ( 1 * sizeof(Conftyp) ) ;
  buff_dock[0].pt =  (Punktyp *) malloc ( LANDS *   sizeof(Punktyp)) ;
 ;

 }


void alloc_intlists(){
    int n;
  firs_conf = malloc ( nuspecs * sizeof (int * ) ) ;
  for ( n =  0 ; n < nuspecs ; n ++)
       firs_conf [n] = malloc ( MAXCATEGS *   sizeof (int    )) ;
  sis_conf = malloc ( nuspecs * sizeof (int * ) ) ;
  for ( n =  0 ; n < nuspecs ; n ++)
     sis_conf  [n] = malloc ( (CONFS +  nuspecs * MAXCATEGS) *   sizeof (int    )) ;
}

void dealloc_matrices (){
 dealloc_branch_labels () ;
 dealloc_datamatrix (  ) ;
 //dealloc_consense_matrix ( nuspecs, NUCATEG, LANDS )  ;
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
   // printf("\nWarning: triangle inequality violated. Fixed");
     }
}

int do_decay (){
int n, yeso, opt_asis,a,b ,vta, falta, old_fac;
double newscore, pace, cto ;
for (n=0 ; n < nnods ; n++){
  if (easy_trans[n][0] == 0 )
    support [n][0]  = 0 ;
  else
    support [n][0] = -1 ;
 if (easy_trans[n][1] == 0 )
    support [n][1]  = 0 ;
  else
    support [n][1] = -1 ;
}
bak_transform();


conf_x_categ (nuspecs,NUCATEG ) ; // llena  nuconf_sp_clas
pace = 0.2; //0.1 ;
vta = 1 ;

old_fac = pen_fac;
pen_orig = penalty ;
if (pen_fac == 0 ) {
 old_fac = pen_fac  ;
 pen_fac = 1 ;
 calculate_penalty (nuspecs,NUCATEG ) ;
}

while (1){
    if (vta > 300)
     break ;
 if (old_fac == 0 )
     penalty = penalty + penalty *( vta - 1) ;
 else
   penalty = penalty + penalty * vta  ;
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
  map_changes(0,-1);
  map_support (0,cto) ; // aca tengo que ver como envio la info. Tengo qeu decidir q info guardo*
  restore_transform() ;
  falta = 0 ;
   for (n=0 ; n < nnods ; n++) {
     if (n == nt )
       continue ;
       if ((support[n][0] == -1 ) || (support[n][1] == -1 ))  {
        falta ++ ;
         break; }
     }
     if (falta == 0 )
      break ;
vta ++ ;
 }
pen_fac  = old_fac ;
penalty = pen_orig  ;
return (1) ;
}


void bak_transform(){
int n ;

for (n=0 ; n < nnods; n ++){
  bak_easy_trans [n][0] = easy_trans[n][0];
  bak_easy_trans [n][1] = easy_trans[n][1];
}
}

void restore_transform(){
int n ;
for (n=0 ; n < nnods; n ++){
   easy_trans[n][0] = bak_easy_trans[n][0] ;
   easy_trans[n][1] = bak_easy_trans[n][1] ;

}
}



void map_support(int qreco, double value){
int n,  std_anc ;
Sank_spcelltyp ** pt_sank ;
pt_sank = sank_mtx ;
fflush(stdout);
 for (n =  0 ; n < nnods ; n++ )
 {
   if (n == nt)
      continue ;
   std_anc = recons[ qreco ][ ances [n] ];
   if ((bak_all_trans[n][5] > 1 ) && (ances [n ] != nt ) ){
     support [n][0] = 0 ;support [n][1] = 0 ;
     continue ; }
   if ((easy_trans[n][0] == 0 ) && (support[n][0] == -1 ) && (easy_trans[n][0] != bak_easy_trans[n][0] ) )
      support [n][0] = value ;
   if ((easy_trans[n][1] == 0 ) && (support[n][1] == -1 ) && (easy_trans[n][1] != bak_easy_trans[n][1] ) )
      support [n][1] = value ;
  }

}//map_support


void do_supports(){
  char nombre [300] ;
  if (do_deca){
      printf("\r                                  ");
      printf("\nCalculating decay values...");
    do_decay() ;

    }
 if ( do_resample ){
   printf("\r                                  ");
   printf("\nPerforming resampling...");
   resample (nuspecs, NUCATEG, extended) ;}
}

int my_spawn_tree_svg(int guich )
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
    if (guich) {
     strcat (name,"_offset_tree.svg");
     fprintf(output_file,"ttag &%s bheight 40   legup 10   txtsep 20  blength 80  color caption In Color Changes at the End of the Ontogeny. Blue= Extended trajectories, Red= Truncated trajectories ;zz;  ",name);
    }
    else{
     strcat (name,"_onset_tree.svg");
     fprintf(output_file,"ttag &%s bheight 40   legup 10  txtsep 20  blength 80 color caption In Color Changes at the Begining of the Ontogeny. Blue= Truncated trajectories, Red= Extended trajectories ;zz;  ",name);
    }
    fclose (output_file);
    strcpy(qqqstr,"tnt ") ; //tiene que ir el nombre del archivo y el del script separado por ;
    strcat (qqqstr,finalFilename) ; //el archivo tnt
    strcat (qqqstr," ") ;
    if (!guich)
     strcat (qqqstr,fintreFilename) ; //el archivo tre con los tags
    else
     strcat (qqqstr,fintreFilename_2) ; //el archivo tre con los tags
     //strcat (qqqstr," colored_tags.txt") ; //el con los tags
    strcat (qqqstr," svg.tmp") ;
    startinfo.cb = sizeof(STARTUPINFO);
    startinfo.lpReserved = NULL;
    startinfo.lpDesktop = NULL;
    wsprintf(jstr,"RUNNING TNT");
    startinfo.lpTitle = jstr;
    startinfo.dwFlags = STARTF_USESHOWWINDOW;
   // startinfo.dwFlags = STARTF_USEPOSITION | STARTF_USESIZE ;
    startinfo.dwX = 25 ;
    startinfo.dwXSize = 350 ;
    startinfo.dwY = 50 ;
    startinfo.dwYSize = 125 ;
    startinfo.cbReserved2 = NULL;

    startinfo.wShowWindow = SW_HIDE;
       if(CreateProcess(NULL, qqqstr, NULL, NULL, FALSE ,
            CREATE_NO_WINDOW , NULL, NULL, &startinfo, &pinfo))
      /* if(CreateProcess(NULL, qqqstr, NULL, NULL, FALSE ,
            HIGH_PRIORITY_CLASS | 0, NULL, NULL, &startinfo, &pinfo))*/
        WaitForSingleObject(pinfo.hProcess,INFINITE);
            else {
                MessageBox(hwnd,"TNT could not be started!","TNT executable should be is in the same folder than SPASOS",MB_OK | MB_ICONERROR );
                return(255);
            }
        GetExitCodeProcess(pinfo.hProcess, &how);
remove ("svg.tmp");

        return( how );
}


make_a_list(){
int i,j,cual ;
Conftyp * pt_conf;
Sptyp * pt_sp ;
pt_sp = sps_list ;
pt_conf = datamatrix ;
output_file = fopen ("list.txt","w");
fprintf(output_file,"\nSpecies,Specimen,stage,Time");
for (  i = 0 ;   i < nuspecs ; i ++ )
 {
 for (j = 0 ;  j < pt_sp[i].num_confs  ; j ++)
  {
  cual = pt_sp[ i ].conflist [ j ] ;
   fprintf(output_file,"\n%s,%s,%i,%f",pt_sp[i].sps_name, datamatrix[cual].ind_number, pt_conf[cual].which_class, pt_conf[cual].age);}}
fclose (output_file);
}



double calculate_disparity (int catg ) {

int i , j , k, van=0, a, infer = -9 , sup = 0,span   ;
double  pace,limms,vza,var;
Punktyp * pt1 ;
Punktyp * pt2 ;
char nombre[50] ;
nombre [0] = NULL;
calculate_consensus_disparity ( catg) ;  // aca calcula una forma promedio para cada stage entre todas las especies

strcat (nombre,prefix);
strcat (nombre,"_disparity.out");
if ( (dispar_file= fopen(nombre, "w")) == NULL){
 printf("\nError while open %s file. Check if a file with the same name is open with another software\n",nombre)  ;
 return ( 0 );
}
fprintf(dispar_file,"Aligned_stg,Disparity,Pairs,Relative\n");
for (a= 0 ; a  < catg; a++)
      disparity [a]= 0 ;


if (dispar_var) {
  for( k = 0 ;  k < catg; k++){
  vza = 0 ;
  van = 0 ;
  for ( i = 0 ;  i < nuspecs; i++){
   if (doasisfiles)
    pt1 = consense_matrix[ i ][k ].pt ;
   else
     pt1 = align_matrix[ i ][k ].pt ;
   pt2 = consense_dispar[ k ].pt ;
   if  ( (pt1->x == -10000001) || (pt2->x == -10000001) )
      continue ;
   var =  pair_conf_dist (pt1, pt2) ;
   var = var * var ;
   vza +=var;
   van++; }
   vanss  [ k ] = van ;
   if (van > 1 )
     disparity[k] = vza/(van - 1 ) ;
   else
     disparity [ k ] = -9 ;
   }
   for (i = 0 ; i < catg; i ++ ){
    if (vanss[i] > 1 ){
       infer = i ; break; }}
   for (i = catg -1  ; i > 0; i -- ){
    if (vanss[i] > 1 ){
       sup = i ; break; }}
}
else
{
 if (doasisfiles){
  for( k = 0 ;  k < catg; k++){
  van= 0 ;
  for ( i = 0 ;  i < nuspecs; i++){
   for ( j = i ;  j < nuspecs; j++){
   if (i == j )continue ;
     pt1 = consense_matrix[ i ][k ].pt ;
     pt2 = consense_matrix[ j ][k ].pt ;
     if  ( ( pt1->x == -10000001 ) || ( pt2->x == -10000001 ))
      continue ;
     disparity [ k ] +=  pair_conf_dist (pt1, pt2) ;
     van++ ; }
      }
    vanss  [ k ] = van ;
    if (van > 0)
     disparity [ k ] =  disparity [ k ] / van ;
    else
     disparity [ k ] = -9 ;
    }
   }
 else{
  for( k = 0 ;  k < catg; k++){
   van= 0 ;
   for ( i = 0 ;  i < nuspecs; i++){
    for ( j = i ;  j < nuspecs; j++){
     if (i == j )continue ;
      pt1 = align_matrix[ i ][k ].pt ;
      pt2 = align_matrix[ j ][k ].pt ;
     if  ( ( pt1->x == -10000001 ) || ( pt2->x == -10000001 ))
      continue ;
     disparity [ k ] +=  pair_conf_dist (pt1, pt2) ;
     van++ ; }
    }
  vanss  [ k ] = van ;
   if (van > 1 && infer == -9 )
        infer = k ;
    if (van <= 1 )
        sup = k -1 ;
    if (van > 0 )
      disparity [ k ] =  disparity [ k ] / van ;
    else
      disparity [ k ] = - 9 ;
  }
  }
}
if (doasisfiles){
 for (k = 0  ; k < catg; k++){
    limms = (double)k / ((double)catg - 1)  ;
    fprintf(dispar_file,"%i, %f, %i, %f\n",k,disparity[k],vanss[k],limms); }
 }
 else{
  span = (sup - infer)    ;
  pace = 1 /(double) span ;
  for (k = 0  ; k < catg; k++){
     if ((k >= infer) && (k <= sup))
      dispar_lim[k] =  pace * ( (double)k - (double) infer) ;}
  for (k = 0  ; k < catg; k++){
    if (disparity [k] == -9 )
      fprintf(dispar_file,"%i, --------,%i, -----\n",k,vanss[k] );
    else
     if  (vanss[k] == 1 )
       fprintf(dispar_file,"%i, %f,%i, -----\n",k,disparity[k],vanss[k]);
     else
       fprintf(dispar_file,"%i, %f,%i, %f\n",k,disparity[k],vanss[k],dispar_lim[k]);}
 }
close (dispar_file) ;
}


calculate_consensus_disparity(int totcats){
int stg, i, l, son ;
Punktyp * conma ;

  for (stg = 0 ;  stg < totcats   ; stg ++)
     consense_dispar[stg].pt[0].x = -10000001 ;


  for (stg = 0 ;  stg < totcats   ; stg ++){
      for (l = 0 ; l < LANDS ; l++){
        buff_dock[0].pt[l].x = 0;  buff_dock[0].pt[l].y = 0; buff_dock[0].pt[l].z = 0; }
      son = 0 ;
      for (i = 0 ;  i < nuspecs ; i ++){
        if (doasisfiles)
          conma = consense_matrix[i][stg].pt ;
        else
           conma = align_matrix[i][stg].pt ;
        if (conma->x == -10000001)
             continue ;
        for (l = 0 ; l < LANDS ; l++){
           buff_dock[0].pt[l].x  +=conma->x ;
           buff_dock[0].pt[l].y  +=conma->y;
           if (DIMS == 3 )
            buff_dock[0].pt[l].z  +=conma->z;
            conma++ ; }
       son ++ ;
      }
      if ( son == 0 ) continue ;
      for (l = 0 ; l < LANDS ; l++){
        consense_dispar[stg].pt[l].x = buff_dock[0].pt[l].x / son ;
        consense_dispar[stg].pt[l].y = buff_dock[0].pt[l].y / son ;
        if (DIMS == 3)
         consense_dispar[stg].pt[l].z = buff_dock[0].pt[l].z / son ;}
    }

}

print_settings ( ) {
 printf("\r                                  ");
 printf("\nSettings:");
 printf("\n---------");
 /*if (timeas)
   printf("\nAge given in continuos scale") ;
 else
   printf("\nAge given as a priori defined stages") ;*/
 if (!dointerp)
   printf("\nUsing interpolating function to fill gaps in the ontogeny",nuconfs ) ;
 if (color_tree)
     printf("\nSvg tree file showing changes at the Offset") ;
 else
     printf("\nSvg tree file showing changes at the Onset") ;


 if (pen_fac == 10000)
    printf("\nAncestral ontogenetic trajectories inferred in the original frame of comparsion");
 printf("\nNumber of Specimens: %i",nuconfs ) ;
 printf("\nNumber of landmarks: %i in %iD",LANDS, DIMS) ;
 printf("\nNumber of Species: %i", nuspecs ) ;
 printf("\nNumber of Stages: %i", NUCATEG ) ;
if (pen_fac != 10000)
 printf("\nPenalty factor= %i",pen_fac);

}

freeing () {
dealloc_matrices () ;
free (consense_dispar);
free (align_matrix) ;
free ( sps_list ) ;
free ( dock1 ) ;
free ( dock2 ) ;
free ( buff_dock ) ;
free (upcosts) ;}




int calculate_windows(){
int  dist, i , j , k  ;
 for (i = 0 ; i< nuspecs ; i++)
  maxdists[i] = -999 ;
 for (i = 0 ; i < nuspecs; i ++){
     for (j = 0 ; j < CAT_INTER;j ++)
       if (yes[i][j]== 1 ){
        dist = 1 ;
        for ( k =  j + 1  ; k < CAT_INTER ; k ++){
         if  (yes[i][k] == 0)
          dist++ ;
          else
            break ;}
       if (dist > maxdists [i] )
         maxdists [i] = 200; //70
      }
   }

}


int interpolate_cont(int cofi,int resa){
int yeso, windsize, cuantas;
      timeas = 1 ;   // ESTO ES PARA TRATAR A LOS DISCRETOS COMO CONTINUOS AL HACER INTERPOLACION

     define_limits (CAT_INTER , nuspecs ) ; // esto lo tengo q hacer siempre xq viene con diferentes configs cuando es dentro de remuestreo aca son 200 categs.

     yeso= sorting_confs_in_cats ( CAT_INTER, nuspecs , cofi ,1 ) ; //aca lleno yes[][]
     fill_order (nuspecs,cofi) ;  // aca lleno van[][] y sis_conf[]  y firs_conf[] es decir que confis van en cada categ de las 20
     fill_trajects_obs () ; // uso van[][] y fistconf[] and sisconf[] para completar traject_obs que tiene 200 categorias y las llena con el promedio
                                 // de las configs observadas en cada categoria.
                                 // En el caso de resampling la matriz original ya fue remuestreada antes de entrar al interp_cont
      calculate_windows() ;  //aca lleno maxdist[s] a partir de yes [][]
     if (dointerp == 1 )
      lookupear_wts () ; // aca lleno wts y uso maxdist.
       //if (dointerp == 2 )
     //lookupear_wts_lin () ;
     if (dointerp == 3 )
      lookupear_wts_div () ;
     do_trajects_interp_fixedpts (resa,0) ;
     do_trajects_interp_fixedpts (resa,1) ;
     //do_trajects_interp_fixedpts_antes (resa) ;
    //do_trajects_interp_fixedpts_nueva(resa) ; // usa YES y wts y llena las 200 categorias de interp_trajec interpolando excepto las que ya estan llenas
                                     // No usa las configuraciones solo la info de iterp_traj cargada en fill_trajects_obs
   if (use_observed)
     fill_dmatrix_winterp (cofi) ; // Aca cargo en dmatrix las configuraciones interpoladas. Ademas // Aca actualiza el numero de configuraciones en cada especie sps_list[s].num_confs.
   else
     fill_dmatrix_winterp_only (cofi) ; // ADEM´AS DE CAMBIAR ESTA FUNCION LO QUE TENGO QUE HACER ES EN DO_TRAJ_INTER-FXD_POINTS QUE NO SKYPEE LOS QUE DICEN yES[I][J] = 1
return (0);
}

print_lynx_StreS(int specie){
int i , conf, l ;
 printf("\n----------------------stre_Start----------------------");
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.338 )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%s/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.338 ) //if (datamatrix[conf].std_sp_age < 0.368 )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%sB/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.472  )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%sC/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
        for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.472  )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%sD/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
}

print_lynx_StreE(int specie){
int i , conf, l ;
 printf("\n----------------------StreE----------------------");
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.338 )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%s/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.338 ) //if (datamatrix[conf].std_sp_age < 0.368 )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%sB/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.338 || datamatrix[conf].std_sp_age > 0.868 )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%sC/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
        for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.338 || datamatrix[conf].std_sp_age > 0.868 )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%sD/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
}


print_lynx_Shift(int specie){ //shift
int i , conf, l ;
  printf("\n----------------------StreE----------------------");
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.562 || datamatrix[conf].std_sp_age > 0.827 ) //if (datamatrix[conf].std_sp_age < 0.368 || datamatrix[conf].std_sp_age > 0.93 ) (datamatrix[conf].std_sp_age < 0.368 || datamatrix[conf].std_sp_age > 0.91 )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%s/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.562 || datamatrix[conf].std_sp_age > 0.827 ) //if (datamatrix[conf].std_sp_age < 0.368 )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%sB/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.562 || datamatrix[conf].std_sp_age > 0.907 ) //if (datamatrix[conf].std_sp_age < 0.458 )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%sC/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
        for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.562 || datamatrix[conf].std_sp_age > 0.907  )
          continue ;
        printf("LM3=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);
        printf("ID=%sD/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
}

print_frogs_shift(int specie){ //shift
int i , conf, l ;
  printf("\n----------------------StreS----------------------\n");
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;
        if (datamatrix[conf].std_sp_age < 0.28198 || datamatrix[conf].std_sp_age > 1.2 ) //0.847 //shift (datamatrix[conf].std_sp_age < 0.403 || datamatrix[conf].std_sp_age > 0.763 )
          continue ;
       if (DIMS == 3){
         printf("LM3=%i\n",LANDS);
         for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);}
       else{
         printf("LM=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y);}
        printf("ID=%s/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;                       //shift (datamatrix[conf].std_sp_age < 0.403 || datamatrix[conf].std_sp_age > 0.763 )
        if (datamatrix[conf].std_sp_age < 0.28198 || datamatrix[conf].std_sp_age > 1.2 ) //0.847
          continue ;
        if (DIMS == 3){
         printf("LM3=%i\n",LANDS);
         for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);}
       else{
         printf("LM=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y);}
        printf("ID=%sB/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
    for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;  // shift (datamatrix[conf].std_sp_age < 0.511 || datamatrix[conf].std_sp_age > 0.877444 )
        if (datamatrix[conf].std_sp_age <   0.28198|| datamatrix[conf].std_sp_age > 0.7846 )
          continue ;
        if (DIMS == 3){
         printf("LM3=%i\n",LANDS);
         for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);}
       else{
         printf("LM=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f\n",datamatrix[conf].pt[l
          ].x,datamatrix[conf].pt[l].y);}
        printf("ID=%sC/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
        for ( i = 0 ; i < sps_list[specie].num_confs; i++){
        conf =  sps_list[specie].conflist[i] ;    // shift(datamatrix[conf].std_sp_age <  0.511 || datamatrix[conf].std_sp_age > 0.877444 )
        if (datamatrix[conf].std_sp_age < 0.28198 || datamatrix[conf].std_sp_age > 0.7846)
          continue ;
       if (DIMS == 3){
         printf("LM3=%i\n",LANDS);
         for (l = 0 ; l < LANDS; l ++)
          printf("%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);}
       else{
         printf("LM=%i\n",LANDS);
        for (l = 0 ; l < LANDS; l ++)
          printf("%f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y);}
        printf("ID=%sD/%i\n",sps_list[specie].sps_name,datamatrix[conf].ind_number) ;
        printf("Age= %f\n",datamatrix[conf].std_sp_age) ;
        }
}


fill_dmatr_w_chsn(){
int s , a , l, obs, vas= 0 ;
Conftyp * pt_dt, * pt_bk ;
//tengo que backapear la conflist de cada especie y ademas modificarla aqui


for (s = 0 ; s < nuspecs ; s ++){
 for (a= 0 ; a < sps_list[s].num_confs ; a++){ //chequear si num_confs fue actualizado con el remuestreo.
  obs = chsn_obs[s][a];
  sps_list[s].conflist[a] = vas ;  //=obs
  for (l = 0 ; l < LANDS; l++){
   datamatrix[vas].pt[l].x = back_mtx[obs].pt[l].x ;
   datamatrix[vas].pt[l].y = back_mtx[obs].pt[l].y ;
   if (DIMS == 3)
    datamatrix[vas].pt[l].z = back_mtx[obs].pt[l].z ;}
  pt_dt = datamatrix ;pt_dt +=vas ;
  pt_bk = back_mtx ; pt_bk+=obs;
  pt_dt->age = pt_bk->age ;
  pt_dt->std_sp_age = pt_bk->std_sp_age ;
  pt_dt->age_aln     = pt_bk->age_aln ;
  pt_dt->sp_number   = pt_bk->sp_number ;
  pt_dt->confnumber  = pt_bk->confnumber ;

  pt_dt->nulands     = pt_bk->nulands ;
  pt_dt->which_class = pt_bk->which_class ;
  pt_dt->which_hyp_class = pt_bk->which_hyp_class ;
  pt_dt->which_str_class = pt_bk->which_str_class ;
  pt_dt->which_aln_class = pt_bk->which_aln_class ;
  strcpy(pt_dt->ind_number,pt_bk->ind_number) ;
  strcpy (pt_dt->sps_name,pt_bk->sps_name) ;
  vas++ ; }}
//ca voy a imprimir la datamatrix

return (vas) ;
}





fill_dmatrix_winterp (int cofi) {
int indnu, cual,s,p,posit,l,conf ;
double span,relpos ;
Conftyp * pt_conf ;
char  * pt_spname, nombre [30];
Punktyp * ptpt, * conpi  ;
Sptyp * pt_sp ;
pt_sp = sps_list ;
pt_conf = datamatrix ;
cual = cofi ;


 for (s = 0 ; s < nuspecs; s ++) {
  posit = pt_sp[s].num_confs ;
  for (p = 0 ; p < CAT_INTER; p ++){
    indnu = 1000 + p  ;
    if (van[s][p] != 0 ) continue ;
      strcpy( pt_conf[cual].sps_name, pt_sp[s].sps_name)  ;
      pt_conf[cual].sp_number = pt_sp[s].sp_number ;
      span =  (pt_sp[s].max_age - pt_sp[s].min_age);
      relpos = (double) p  /  ( (double) CAT_INTER  - 1) ;
      pt_conf[cual].age =  span * relpos + pt_sp[s].min_age ;
      sprintf(nombre, "%d", indnu);
      strcpy(pt_conf[cual].ind_number, nombre) ;
      pt_conf[cual].nulands = LANDS ;
      pt_sp[s].conflist[posit] = cual ;
      pt_conf[cual].std_sp_age =  (pt_conf[cual].age - pt_sp[s].min_age)  / (pt_sp[s].max_age - pt_sp[s].min_age)  ;
      conpi   =  interp_trajec [ s ][ p ].pt;
      ptpt = pt_conf [ cual ].pt ;
      for (l = 0 ; l < LANDS ; l++){
        ptpt->x  =  conpi->x   ;
        ptpt->y  =  conpi->y   ;
        ptpt->z  =  conpi->z   ;
        ptpt++;conpi++; }
      posit ++ ; cual++;
      }
      pt_sp[s].num_confs = posit ;
      }
}




fill_dmatrix_winterp_only (int cofi) { // aca tengo que modificarlo para empezar desde 0 en cada especie ya q me cago en lo observado
int indnu, cual,s,p,posit,l ;
double span,relpos ;
Conftyp * pt_conf ;
char  * pt_spname, nombre [300];
Punktyp * ptpt, * conpi  ;
Sptyp * pt_sp ;
pt_sp = sps_list ;
pt_conf = datamatrix ;
cual = 0;

// cual son el numero de configs observadas que aca tiene que ser 0 al ppio
// posit empieza en cero en todas las especies
 for (s = 0 ; s < nuspecs; s ++) {
  posit = 0 ;
  for (p = 0 ; p < CAT_INTER; p ++){
    indnu = 1000 + p  ;
      if (p ==  0) pt_sp[s].confminage = cual;
      if (p == (CAT_INTER-1)) pt_sp[s].confmaxage = cual;
      strcpy( pt_conf[cual].sps_name, pt_sp[s].sps_name)  ;
      pt_conf[cual].sp_number = pt_sp[s].sp_number ;
      span =  (pt_sp[s].max_age - pt_sp[s].min_age);
      relpos = (double) p  /  ( (double) CAT_INTER  - 1) ;
      pt_conf[cual].age =  span * relpos + pt_sp[s].min_age ;
      sprintf(nombre, "%d", indnu);
      strcpy(pt_conf[cual].ind_number, nombre) ;
      //pt_conf[cual].ind_number = indnu ;
      pt_conf[cual].nulands = LANDS ;
      pt_conf[cual].confnumber ;
      pt_sp[s].conflist[posit] = cual ;
      pt_conf[cual].std_sp_age =  (pt_conf[cual].age - pt_sp[s].min_age)  / (pt_sp[s].max_age - pt_sp[s].min_age)  ;
      conpi   =  interp_trajec [ s ][ p ].pt;
      ptpt = pt_conf [ cual ].pt ;
      for (l = 0 ; l < LANDS ; l++){
        ptpt->x  =  conpi->x   ;
        ptpt->y  =  conpi->y   ;
        ptpt->z  =  conpi->z   ;
        ptpt++;conpi++; }
      posit ++ ; cual++;
      }
      pt_sp[s].num_confs = posit ;
      }
}





do_trajects_interp_revised(int vuelta) {
int s,a, p,f,g,i, pts_izq, pts_der,l, q, peso, confi,halfw, ctos ,dists[200],tmpL_pi,tmp_qs[100],pos_izq,pos_der, guer;
double wts_pos, wts_dist, dist, wts_izq, wts_der,all_wts,thwts,tmp_p,peso_izq,peso_der ;
char nombre [50];
char str[10];
double wts_num[2], prod_wts[100] ;
double * wt_pt, * pd_pt;
Punktyp * conpi, *conq, *conq2 ;
Conftyp * pt_conf , *conse_izq, *conse_der ;
Sptyp * pt_sp ;
pt_sp = sps_list ;
conse_izq = (Conftyp *) malloc ( 1 * sizeof(Conftyp) ) ;
conse_izq[0].pt =  (Punktyp *) malloc ( LANDS *   sizeof(Punktyp)) ;
conse_der = (Conftyp *) malloc ( 1 * sizeof(Conftyp) ) ;
conse_der[0].pt =  (Punktyp *) malloc ( LANDS *   sizeof(Punktyp)) ;


for (a=0; a < LANDS; a++){
   conse_izq[0].pt[a].x = 0;conse_izq[0].pt[a].y = 0;conse_izq[0].pt[a].z = 0;}
nombre[0] = NULL  ;
str[0] = NULL ;
wt_pt =& wts_num ;
pd_pt =& prod_wts;
 for (s = 0 ; s < nuspecs; s ++) {
   for (p = 0 ; p < CAT_INTER; p ++){
      if (use_observed)
         if (yes[s][p] == 1) continue ;
      sum_wts_fxd_antes (s,p,FXDPTS,wt_pt,pd_pt,0); //cargo wts_num y prod_wts con los pesos si hay menos de 3 wts -> -1
      if (wts_num[0] < wts_num[1])
        wts_num[1] = wts_num[0];
      else
        wts_num[0] = wts_num[1];
      for (i = wts_num[0] ; i < FXDPTS ; i ++)
        prod_wts[i] = -1 ;
      for (i = FXDPTS + wts_num[0] ; i <  2 * FXDPTS  ; i ++)
        prod_wts[i] = -1 ;

      all_wts = 0 ; dist = 0 ; ctos = 0 ;
      dde =0 ;
      for ( q= p -1  ; q >= 0 ; q-- ){
       if ((dde == FXDPTS )|| (prod_wts[dde] == -1 )) break ;
        if ( van[s][q] != 0){
         dists[dde] = p - q ;
         tmp_qs [dde] = q  ;
         all_wts += wts[s][ dists[dde]] ;
         dde++; }
         }
      for (a=0; a < LANDS; a++){
        conse_izq[0].pt[a].x = 0;conse_izq[0].pt[a].y = 0;conse_izq[0].pt[a].z = 0;}
      for ( f = 0  ; f < dde ; f ++ ){
        g =  tmp_qs [f] ;
        conq   =  interp_trajec [ s ][ g ].pt;
        peso_izq = wts[s][ dists [ f ] ]  / all_wts ;
        for (l = 0 ; l < LANDS ; l++) {
         conse_izq[0].pt[l].x  = conse_izq[0].pt[l].x + conq->x * peso_izq   ;
         conse_izq[0].pt[l].y  = conse_izq[0].pt[l].y + conq->y * peso_izq   ;
         conse_izq[0].pt[l].z  = conse_izq[0].pt[l].z + conq->z * peso_izq   ;
            conq++;  } }
       pos_izq = tmpL_pi ;

      all_wts = 0 ; dist = 0 ; ctos = 0 ;
      dde = FXDPTS ;
      guer = 0 ; all_wts = 0 ;
      for ( q= p + 1  ; q <  CAT_INTER ; q++ ){
       if ((dde == ( 2* FXDPTS)  )|| (prod_wts[dde] == -1 )) break ;
        if ( van[s][q] != 0){
          dists[guer] = q - p  ;
          tmp_qs [guer] = q  ;
          all_wts += wts[s][ dists[guer]] ;
         dde++;guer++;
        }}
      for (a=0; a < LANDS; a++){
       conse_der[0].pt[a].x = 0;conse_der[0].pt[a].y = 0;conse_der[0].pt[a].z = 0;}
      for ( f = 0  ; f < guer ; f ++ ){
        g =  tmp_qs [f] ;
        conq   =  interp_trajec [ s ][ g ].pt;
        peso_der = wts[s][ dists [ f ] ] / all_wts  ;
        for (l = 0 ; l < LANDS ; l++) {
         conse_der[0].pt[l].x  = conse_der[0].pt[l].x +  conq->x * peso_der   ;
         conse_der[0].pt[l].y  = conse_der[0].pt[l].y + conq->y * peso_der   ;
         conse_der[0].pt[l].z  = conse_der[0].pt[l].z + conq->z * peso_der   ;
            conq++;  } }
       pos_der = tmpL_pi ;

       conpi  =  interp_trajec [ s ][ p ].pt;
       conq   =  conse_izq[0].pt;
       conq2  =  conse_der[0].pt ;
       peso_izq = wts[s][ p - pos_izq ] ;
       peso_der = wts[s][ pos_der - p ] ;
       all_wts= peso_izq + peso_der ;
       peso_izq /=all_wts ;
       peso_der /=all_wts ;
       for (l = 0 ; l < LANDS ; l++) {
         conpi->x  = conq->x * peso_izq +  conq2->x * peso_der   ;
         conpi->y  = conq->y * peso_izq +  conq2->y * peso_der   ;
         conpi->z  = conq->z * peso_izq +  conq2->z * peso_der   ;
         conq++; conpi ++ ; conq2++; }
  }
 }

return ;

if (vuelta > 0 )
 return ;
 nombre[0] = NULL ;
strcat(nombre,prefix);
sprintf(str, "%d", vuelta);
strcat(nombre,str);
strcat(nombre,"_iterpo_specs.tps");
sank_file= fopen(nombre, "w");
 fprintf(sank_file,"\n");
for (s = 0 ; s < nuspecs; s ++) {
  for (p = 0 ; p < CAT_INTER; p ++){
    if (DIMS == 3 )
     fprintf(sank_file,"LM3=%i\n",LANDS);
    else
       fprintf(sank_file,"LM=%i\n",LANDS);
   for (l = 0 ; l < LANDS; l ++){
       if (DIMS == 3)
        fprintf(sank_file,"%f %f %f\n",interp_trajec [ s ][ p ].pt[l].x,interp_trajec [ s ][ p ].pt[l].y,interp_trajec [ s ][ p ].pt[l].z);
       else
         fprintf(sank_file,"%f %f \n",interp_trajec [ s ][ p ].pt[l].x,interp_trajec [ s ][ p ].pt[l].y);
        }
   if(van[s][p] == 0 )
     fprintf(sank_file,"ID=%s_stg%iInt_%i%i\n",pt_sp[s].sps_name,p,vuelta,p) ;
   else
     fprintf(sank_file,"ID=%s_stg%i_%i\n",pt_sp[s].sps_name,p,vuelta) ; }
   }
fclose (sank_file);

nombre[0] = NULL ;
strcat(nombre,prefix);
sprintf(str, "%d", vuelta);
strcat(nombre,str);
strcat(nombre,"_iterpo_covar.txt");
sank_file= fopen(nombre, "w");
for (s = 0 ; s < nuspecs; s ++)
 for (p = 0 ; p < CAT_INTER; p ++){
   if(van[s][p] == 0 )
     fprintf(sank_file, "%s_stg%iInt_%i%i,%i\n",pt_sp[s].sps_name,p,vuelta,p,p ) ;
   else
    fprintf(sank_file, "%s_stg%i_%i,%i\n",pt_sp[s].sps_name,p,vuelta,p ); }
fclose (sank_file);

nombre[0] = NULL ;
strcat(nombre,prefix);
sprintf(str, "%d", vuelta);
strcat(nombre,str);
strcat(nombre,"_iterpo_class.txt");
sank_file= fopen(nombre, "w");

for (s=0 ; s < nuspecs; s++ )
 for (p=0 ; p < CAT_INTER; p++ ) {
    if(van[s][p] == 0 )
     fprintf(sank_file,"%s_stg%iInt_%i%i,%s_%i,INT\n",sps_list[ s].sps_name,p,vuelta,p,sps_list[ s].sps_name,vuelta);
    else
     fprintf(sank_file,"%s_stg%i_%i,%s_%i,OBS\n",sps_list[ s].sps_name,p,vuelta,sps_list[ s].sps_name,vuelta);}
fclose (sank_file);

}



do_trajects_interp_fixedpts(int vuelta,int segunda) { //marzo
int s,a, p, pts_izq, pts_der,l, q, peso, confi,halfw, ctos ;
double wts_pos, wts_dist, wts_izq, wts_der,all_wts,thwts ;
char nombre [50];
char str[10];
double wts_num[2], prod_wts[100] ;
double * wt_pt, * pd_pt;
Punktyp * conpi, *conq ;
Conftyp * pt_conf ;
Sptyp * pt_sp ;
pt_sp = sps_list ;
nombre[0] = NULL  ;
str[0] = NULL ;
wt_pt =& wts_num ;
pd_pt =& prod_wts;
 // PARA PROBAR SOLO LOS INFERIDOS NO TIENE QUE  SKYPEAR LOS QUE DICEN yES[I][J] = 1


  for (s = 0 ; s < nuspecs; s ++) {
   for (p = 0 ; p < CAT_INTER; p ++){
        if ( use_observed || (!segunda) )
          if (yes[s][p] == 1) continue ;
         sum_wts_fxd_antes(s,p,FXDPTS,wt_pt,pd_pt,segunda); //cargo wts_num y prod_wts con los pesos si hay menos de 3 wts -> -1
         if (wts_num [0] == 0 )
           wts_num[1] = 1 / wts_num[1] ;
         else
           wts_num[1] = 0.5 * ( 1 / wts_num[1]) ;
         if (wts_num [1] == 0 )
           wts_num[0] = 1 / wts_num[0] ;
         else
           wts_num[0] = 0.5 *( 1 / wts_num[0]) ;
         for (a =  0 ;a < FXDPTS ; a ++ ) //lupea las posiciones izq de de prod_wts
          if (prod_wts[a]!= -1)
            prod_wts [ a ] *=wts_num[0];
         for (a =  FXDPTS ;a < (2 * FXDPTS) ; a ++ )//lupea las posiciones der de de prod_wts
           if (prod_wts[a]!= -1)
            prod_wts [ a ] *=wts_num[1];
         all_wts = 0 ;

         for ( a =  0 ; a < (2 * FXDPTS) ; a ++ )//sumo todos los productos
          if (prod_wts[a]!= -1)
            all_wts += prod_wts[a];
          /*if (s == 0 )
            printf("\npivot=%i",p);*/
          for ( a =  0 ; a < (2 * FXDPTS) ; a ++ ){// relativizo los pesos
             if (prod_wts[a]!= -1)
               prod_wts[a] /= all_wts;
          //if (s==0)printf("\n%i,%f",a,prod_wts[a]);
          }

                 conpi = interp_trajec [ s ][ p ].pt;
         for (l = 0 ; l < LANDS ; l++){
          conpi->x = 0; conpi->y = 0;conpi->z = 0; conpi++ ; }
         conpi = interp_trajec [ s ][ p ].pt;
         ctos = 0 ;
        for ( q= p -1  ; q >= 0 ; q-- ){
          if ((ctos == FXDPTS )|| (prod_wts[ctos] == -1 )) break ;
          if ( van[s][q] != 0 || segunda ){
           conpi   =  interp_trajec [ s ][ p ].pt;
           conq    =  interp_trajec [ s ][ q ].pt ;
           for (l = 0 ; l < LANDS ; l++){
            conpi->x  = conpi->x + ( conq->x * prod_wts[ctos] ) ;
            conpi->y  = conpi->y + ( conq->y * prod_wts[ctos] ) ;
            conpi->z  = conpi->z + ( conq->z * prod_wts[ctos] ) ;
            conpi++;conq++; }
            ctos++ ;
            //if (s==0)printf("\nIZQ, %i,%i",q,ctos) ;
            }
            }

          ctos = FXDPTS ;
          for ( q= p +1  ; q < CAT_INTER ; q++ ){
           if ((ctos == ( FXDPTS * 2)) || (prod_wts[ctos] == -1 ) ) break ;
           if ( van[s][q] != 0 || segunda ){
           conpi   =  interp_trajec [ s ][ p ].pt;
           conq    =  interp_trajec [ s ][ q ].pt ;
           for (l = 0 ; l < LANDS ; l++){
            conpi->x  = conpi->x + ( conq->x * prod_wts[ctos] ) ;
            conpi->y  = conpi->y + ( conq->y * prod_wts[ctos] ) ;
            conpi->z  = conpi->z + ( conq->z * prod_wts[ctos] ) ;
            conpi++;conq++;}
            ctos++;
           //if (s==0) printf("\nDER, %i,%i",q,ctos) ;
           }

         }
   }
 }
return ;
if (segunda == 0 || vuelta > 0   )
return ;
nombre[0] = NULL ;
strcat(nombre,prefix);
sprintf(str, "%d", vuelta);
strcat(nombre,str);
strcat(nombre,"_iterpo_specs.tps");
sank_file= fopen(nombre, "w");
 fprintf(sank_file,"\n");
for (s = 0 ; s < nuspecs; s ++) {
  for (p = 0 ; p < CAT_INTER; p ++){
    if (DIMS == 3 )
     fprintf(sank_file,"LM3=%i\n",LANDS);
    else
       fprintf(sank_file,"LM=%i\n",LANDS);
   for (l = 0 ; l < LANDS; l ++){
       if (DIMS == 3)
        fprintf(sank_file,"%f %f %f\n",interp_trajec [ s ][ p ].pt[l].x,interp_trajec [ s ][ p ].pt[l].y,interp_trajec [ s ][ p ].pt[l].z);
       else
         fprintf(sank_file,"%f %f \n",interp_trajec [ s ][ p ].pt[l].x,interp_trajec [ s ][ p ].pt[l].y);
        }
   if(van[s][p] == 0 )
     fprintf(sank_file,"ID=%s_stg%iInt_%i%i\n",pt_sp[s].sps_name,p,vuelta,p) ;
   else
     fprintf(sank_file,"ID=%s_stg%i_%i\n",pt_sp[s].sps_name,p,vuelta) ; }
   }
fclose (sank_file);

nombre[0] = NULL ;
strcat(nombre,prefix);
sprintf(str, "%d", vuelta);
strcat(nombre,str);
strcat(nombre,"_iterpo_covar.txt");
sank_file= fopen(nombre, "w");
for (s = 0 ; s < nuspecs; s ++)
 for (p = 0 ; p < CAT_INTER; p ++){
   if(van[s][p] == 0 )
     fprintf(sank_file, "%s_stg%iInt_%i%i,%i\n",pt_sp[s].sps_name,p,vuelta,p,p ) ;
   else
    fprintf(sank_file, "%s_stg%i_%i,%i\n",pt_sp[s].sps_name,p,vuelta,p ); }
fclose (sank_file);

nombre[0] = NULL ;
strcat(nombre,prefix);
sprintf(str, "%d", vuelta);
strcat(nombre,str);
strcat(nombre,"_iterpo_class.txt");
sank_file= fopen(nombre, "w");

for (s=0 ; s < nuspecs; s++ )
 for (p=0 ; p < CAT_INTER; p++ ) {
    if(van[s][p] == 0 )
     fprintf(sank_file,"%s_stg%iInt_%i%i,%s_%i,INT\n",sps_list[ s].sps_name,p,vuelta,p,sps_list[ s].sps_name,vuelta);
    else
     fprintf(sank_file,"%s_stg%i_%i,%s_%i,OBS\n",sps_list[ s].sps_name,p,vuelta,sps_list[ s].sps_name,vuelta);}
fclose (sank_file);
}//do_trajects_interp



double sum_wts(int sps,int pivot,int wisiz){
 int peso, q, halfw ;
 double sumwts= 0  ;
 halfw = wisiz / 2 ;
    for (q= (pivot - halfw ) ; q < (pivot + halfw + 1) ; q++){
       if ( (q < 0) || (q >= CAT_INTER) || (van[sps][q] == 0)  )
         continue ;
       peso = q - pivot ;
       if ( peso < 0 ) peso = - peso ;
       sumwts +=wts [sps][ peso ] ;}
 return (sumwts);
 }//sum_wts

double sum_wts_fxd_antes(int sps,int pivot,int winsizfxd, double *  wts_pt, double * prod_pt, int segunda){
 int peso, q,i, halfw, ctos = 0,dde  ;
 double sumwts= 0  ;
 for (i = 0 ; i < 99  ; i ++)
        prod_pt[i] = -1 ;  ;


dde =  0; //VER SI ESTE DESDE NO ASUME Q SON 3 SI ES ASI CAMBIAR
 for ( q= pivot -1  ; q >= 0 ; q-- )
      {
       if ( van[sps][q] != 0 || segunda){
        if ( ( pivot - q )  >  ( maxdists[sps] ) )
          break;
        ctos++ ; //ESTO LO CAMBIE DE LUGAR
        prod_pt[dde] = wts [sps][pivot-q] ;
        dde ++ ;
       }
       if ( ctos ==  winsizfxd )
         break ;
      }
 dde = winsizfxd  ;
 wts_pt[0] = (double) ctos ;
 ctos = 0 ;
 for ( q= pivot + 1 ; q < CAT_INTER ; q++ ){
       if ( van[sps][q] != 0 || segunda ){
        if ( (q - pivot )  >  ( maxdists[sps]  ) )
          break;
        ctos++ ;
        prod_pt[dde] = wts [sps][q-pivot];
        dde++ ;
       }
       if ( ctos ==  winsizfxd )
         break ;
     }
     wts_pt[1] = (double) ctos;

 if (wts_pt[0] < wts_pt[1])
   wts_pt[1] = wts_pt[0];
 else
   wts_pt[0] = wts_pt[1];
 for (i = wts_pt[0] ; i < FXDPTS ; i ++)
   prod_pt[i] = -1 ;
 for (i = FXDPTS + wts_pt[0] ; i <  2 * FXDPTS  ; i ++)
   prod_pt[i] = -1 ;
 return (sumwts);
 }//sum_wts_fxd



lookupear_wts (){ // voy a calcular el weight para diferencias de x celdas
int i, halfint,s, ventana_i ;
double z,halfw, ventana_d ;


 for (s=0; s< nuspecs ; s ++){
      halfint = (maxdists[s] + 1 )   ;
      for (i = 0 ; i < halfint ; i ++) {              //for (i = 0 ; i <  halfint + 1 ; i++ ){
       halfw = (double) maxdists[s] + 1    ;
       z = (double) i / halfw ;
       z = pow (z,3) ;
       z = 1 - z ;
       z = pow (z,3);
       wts [s][ i ] = z ;}}
}//lookupear_wts



lookupear_wts_lin (){ // voy a calcular el weight para diferencias de x celdas
int i, halfint,s ;
double z,halfw ;
 for (s=0; s< nuspecs ; s ++){
   halfint = (maxdists[s] + 1)  / 2  ;
   for (i = 0 ; i <  halfint + 1 ; i++ ){
       halfw = (double) (maxdists[s] +1 )/ 2 ;
       z =   (halfint - (double) i) / halfw ;
       wts [s][ i ] = z ;}}
}//lookupear_wts_lin


lookupear_wts_div (){ // voy a calcular el weight para diferencias de x celdas
int i, halfint,s ;
double z,halfw ;
 for (s=0; s< nuspecs ; s ++){
   halfint = (maxdists[s] + 1)    ; //(maxdists[s] + 1)  / 2  ;
   for (i = 1 ; i <  halfint  ; i++ ){
       z = 1 / (double) i ;     //z =   1  / pow((double) i,2) ;
       wts [s][ i ] = z ;}}
}//lookupear_wts_div




 int hmdatapts (int spc, int side, int pivot,int winsize){
 int q, son= 0  ;
      if (side < 0 ){
        for (q = ( pivot -  (winsize/2) ) ; q < pivot  ; q++){
         if (q < 0 ) continue ;
         if (van[spc][q] != 0)
            son++ ;} }
      else {
         for (q = pivot ; q < ( pivot +  (winsize/2) ) ; q++){
          if (q >= CAT_INTER) continue ;
          if (van[spc][q] != 0)
            son++ ;} }
 return (son);
}//hmdatapts

fill_trajects_obs () {
int s, t,l,a,confi,son ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
Punktyp * conma ;
pt_conf = datamatrix ;
  for (s = 0 ; s < nuspecs ; s++)
   {
    for (t = 0 ; t < CAT_INTER ; t++)
     {
      if (van [s][t]== 0 ) continue ;
      conma = interp_trajec [ s ][ t ].pt;
      for (l = 0 ; l < LANDS ; l++){
        conma->x = 0; conma->y = 0;conma->z = 0; conma++ ; }
      confi = firs_conf[s][t];
      conma = interp_trajec [ s ][ t ].pt;
      for (l = 0 ; l < LANDS ; l++){
            conma->x  +=pt_conf[confi].pt[l].x ;
            conma->y  +=pt_conf[confi].pt[l].y;
            conma->z  +=pt_conf[confi].pt[l].z;
            conma++; }

      for (a= 0 ; a < van[s][t]; a++)
       {
        if (sis_conf[s][confi] == -999)
         break ;
        confi =sis_conf[s][confi] ;
        conma = interp_trajec [ s ][ t ].pt;
        for (l = 0 ; l < LANDS ; l++){
            conma->x  +=pt_conf[confi].pt[l].x ;
            conma->y  +=pt_conf[confi].pt[l].y;
            conma->z  +=pt_conf[confi].pt[l].z;
            conma++; }
       }
      conma = interp_trajec [s][t].pt;
      son = van [s][t] ;
      for (l = 0 ; l < LANDS ; l++){
          conma->x  =  conma->x  / son ;
          conma->y  =  conma->y  / son ;
          conma->z  =  conma->z  / son ; conma++ ;}
      }
   }
} // fill_trajects





fill_order(int nusp, int nucon){
int s,t,c,previa,ctos,confi,stg_conf,i,a,p;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_sp = sps_list ;
pt_conf = datamatrix ;

  for (s = 0 ; s < nusp; s ++)
   for (p = 0 ; p < CAT_INTER; p ++)
      van[s][p] = 0 ;
for (s = 0 ; s < nusp ; s++)
  for (t = 0 ; t < CAT_INTER ; t++)
   firs_conf[s][t] = -999 ;
for (s = 0 ; s < nusp ; s++)
  for (t = 0 ; t <   nucon   ; t++)
     sis_conf [s][t] = -999 ;

for (s = 0 ; s < nusp ; s++){
  for (c = 0 ; c < pt_sp[s].num_confs ; c++){
    confi = pt_sp[s].conflist[c] ;
    stg_conf = pt_conf[confi].which_class;
    if (firs_conf[s][stg_conf] == -999 ){
      firs_conf[s][stg_conf] = confi ;
      van  [s][stg_conf] ++; }
    else{
     ctos = van [s][stg_conf] ;
     if (ctos == 1 ){
        previa = firs_conf[s][stg_conf];
        sis_conf[s][previa] = confi ;
        van [s][stg_conf] ++ ;}
     else{
        previa = firs_conf[s][stg_conf];
        for (i= 0 ; i < (ctos - 1) ; i++)
          previa =  sis_conf[s][previa] ;
        sis_conf[s][previa] = confi;
        van [s][stg_conf] ++ ;     }
      }
      }
  }

}//fill_order



do_gapped_trajects_categs(){
int a,b,i,s,l,c,conf,ra, mentos,j,nop,rands[3000],rr,k, exclude,g,lacagamos ;
double step, minlimgap,maxlimgap, fra,frags[2][20] ;
char nume [20], nombre [200],numm[10] ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_sp = sps_list ;
pt_conf = datamatrix ;

for (a= 0 ; a < nuspecs; a ++)
 for (b= 0 ; b < MAXINDXSP; b ++)
  excl[a][b]= 0 ;
  nombre[0] = NULL;
    nume[0] = NULL;
    numm[0]= NULL;
    itoa (i,nume,10);
    itoa (gap_fac,numm,10);
    strcat(nombre,numm);
    strcat(nombre,"_");
    strcat(nombre,nume);
    strcat(nombre,"_ONEsps_gapped_frag.tps");
    output_file= fopen(nombre, "w");
  pt_sp = sps_list ;
  for (s= 0 ; s < nuspecs; s++){
   for (c =  0; c < pt_sp->num_confs ; c ++)
       {
       conf =   pt_sp->conflist[c] ;
       if (s > 1 )// para casos con 4 especies.
        {
        if (datamatrix[conf].age != 0 && datamatrix[conf].age != 3 && datamatrix[conf].age != 5){
         continue ;
         }
        }
        if (DIMS == 2 )
         fprintf(output_file,"LM=%i\n",LANDS);
        else
         fprintf(output_file,"LM3=%i\n",LANDS);

        for (l = 0 ; l < LANDS ; l ++){
         if (DIMS == 2 )
           fprintf(output_file,"%f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y);
        else
           fprintf(output_file,"%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);}
       fprintf(output_file,"ID=%s/%i\n",pt_sp->sps_name,datamatrix[conf].ind_number);
       fprintf(output_file,"Age=%.0f\n",datamatrix[conf].age);
       }
  pt_sp++;
  }
fflush(output_file) ;
close (output_file);
}






do_gapped_trajects_fragm(){
int a,b,i,s,l,c,conf,hmn,ra, mentos,j,nop,rands[3000],rr,k, exclude,g,lacagamos ;
double step, minlimgap,maxlimgap, fra,frags[2][20] ;
char nume [20], nombre [200],numm[10] ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_sp = sps_list ;
pt_conf = datamatrix ;
srand(time(0));
mentos = 6 ;
for (a= 0 ; a < nuspecs; a ++)
 for (b= 0 ; b < sps_list[a].num_confs; b ++)
  excl[a][b]= 0 ;


 for ( i = 0 ;  i < 100 ; i ++) { //hago 10 replicas
    pt_sp = sps_list ;
    nombre[0] = NULL;
    nume[0] = NULL;
    numm[0]= NULL;
    itoa (i,nume,10);
    itoa (gap_fac,numm,10);
    strcat(nombre,numm);
    strcat(nombre,"_");
    strcat(nombre,nume);
    strcat(nombre,"_ONEsps_gapped_frag.tps");
    output_file= fopen(nombre, "w");
    for (a= 0 ; a < nuspecs; a ++)
      for (b= 0 ; b < MAXINDXSP; b ++)
       excl[a][b]= 0 ;
     for (k= 0 ; k < 3000 ; k ++)
        rands [ k ] = rand() % 100 ;
    for ( s = 0 ;  s < nuspecs; s ++)
     {
     // printf("\nincluidas") ;
      if (gap_fac  < 10)
        step = (pt_sp->max_age - pt_sp->min_age )/(double) gap_fac  ;
      else{
        step = (pt_sp->max_age - pt_sp->min_age) * ((double)gap_fac/100)  ;
          mentos = 6 ;  }//mentos = 15 ;
      fra = step / mentos ;
      hmn = 0 ;
      rr = 0 ; lacagamos = 0 ;
      while (1) {
       hmn = 0 ;
       rr = lacagamos ;
       while (hmn < mentos){
        frags[0][hmn] = pt_sp->min_age + ((pt_sp->max_age - pt_sp->min_age) * ((double) rands[rr] / 100)) ;
        frags[1][hmn] = frags[0][hmn] +  fra ;
        rr ++ ;
        if (rr > 2999){
          lacagamos ++ ;
          break;}
        if (frags[1][hmn] > pt_sp->max_age) continue ;
        nop =  0;
        if (hmn != 0 ) {
         for (j = 0 ; j < hmn ; j++){
           if ( ((frags[0][hmn] >= frags[0][j]) &&  ( frags[0][hmn] <= frags[1][j])) || ((frags[1][hmn] >= frags[0][j]) &&  (frags[1][hmn] <= frags[1][j])))
            nop ++ ;   }
         }
        if (nop == 0)
         hmn++ ;
         if (hmn == mentos){
             lacagamos = 0 ;
             break ;}
       }
       if (lacagamos ==  0)
         break ;
       }
     if (lacagamos > 2999)
       break ;

     for (c =  0; c < pt_sp->num_confs ; c ++)
       {
       conf =   pt_sp->conflist[c] ;
       if (s > 1 )// para casos con 4 especies.
        {
        exclude = 0 ;
        if (conf != pt_sp->confminage && conf != pt_sp->confmaxage ){
         for (g= 0 ; g < mentos ; g++)
            {
           if ( datamatrix[conf].age > frags[0][g] && datamatrix[conf].age <  frags[1][g])
              exclude ++ ;
             }
          }
          if (exclude){
            excl[s][conf] = 1 ;
           continue ;}
        }
        if (DIMS == 2 )
         fprintf(output_file,"LM=%i\n",LANDS);
        else
         fprintf(output_file,"LM3=%i\n",LANDS);

        for (l = 0 ; l < LANDS ; l ++){
         if (DIMS == 2 )
           fprintf(output_file,"%f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y);
        else
           fprintf(output_file,"%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);}
       fprintf(output_file,"ID=%s/%i\n",pt_sp->sps_name,datamatrix[conf].ind_number);
       fprintf(output_file,"Age=%f\n",datamatrix[conf].age);
       }
     pt_sp++;
     }
     fflush(output_file) ;
     close (output_file);
 }
}




do_gapped_trajects_cont(){
int i,s,l,c,conf  ;
double step, minlimgap,maxlimgap ;
char nume [20], nombre [200],numm[10] ;
Sptyp * pt_sp ;
Conftyp * pt_conf ;
pt_sp = sps_list ;
pt_conf = datamatrix ;

if (gap_fac > 48)
  return ;
  for ( i = 0 ;  i <  gap_fac ; i ++) {
    pt_sp = sps_list ;
    nombre[0] = NULL;
    nume[0] = NULL;
    numm[0]= NULL;
    itoa (i,nume,10);
    itoa (gap_fac,numm,10);
    strcat(nombre,numm);
    strcat(nombre,"_");
    strcat(nombre,nume);
    strcat(nombre,"_ONEsps_gapped_cont.tps");
    output_file= fopen(nombre, "w");
    for ( s = 0 ;  s < nuspecs; s ++)
     {
     // printf("\nincluidas") ;
      step = (pt_sp->max_age - pt_sp->min_age )/(double)gap_fac ;
      minlimgap = pt_sp->min_age + ( step * i) ;
      maxlimgap = pt_sp->min_age + step * i + step ;
     for (c =  0; c < pt_sp->num_confs ; c ++)
       {
       conf =   pt_sp->conflist[c] ;
       if (s > 1 )// para casos con 4 especies.
        {
        if (conf != pt_sp->confminage && conf != pt_sp->confmaxage )
         if ( datamatrix[conf].age > minlimgap && datamatrix[conf].age <  maxlimgap)
          continue ;}
        if (DIMS == 2 )
         fprintf(output_file,"LM=%i\n",LANDS);
        else
         fprintf(output_file,"LM3=%i\n",LANDS);

        for (l = 0 ; l < LANDS ; l ++){
         if (DIMS == 2 )
           fprintf(output_file,"%f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y);
        else
           fprintf(output_file,"%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);}
       fprintf(output_file,"ID=%s/%i\n",pt_sp->sps_name,datamatrix[conf].ind_number);
       fprintf(output_file,"Age=%f\n",datamatrix[conf].age);
       }
     pt_sp++;
     }
     fflush(output_file) ;
     close (output_file);
 }
}

give_original(int sps){
int c,l, conf,s;
output_file= fopen ("configs_ng.tps","w+");
for (s=0 ; s< nuspecs; s++){
  sps = s ;
  for (c =  0; c < sps_list[sps].num_confs ; c ++){
    conf =   sps_list[sps].conflist[c] ;
        if (DIMS == 2 )
          fprintf(output_file,"LM=%i\n",LANDS);
        else
         fprintf(output_file,"LM3=%i\n",LANDS);

        for (l = 0 ; l < LANDS ; l ++){
         if (DIMS == 2 )
           fprintf(output_file,"%f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y);
        else
           fprintf(output_file,"%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);}
       fprintf(output_file,"ID=%sNG/%i\n",sps_list[sps].sps_name,datamatrix[conf].ind_number);
       }
}
close (output_file);

output_file = fopen ("cova.out","w+");
for (s=0 ; s< nuspecs; s++){
  sps = s ;
  for (c =  0; c < sps_list[sps].num_confs ; c ++){
    conf =   sps_list[sps].conflist[c] ;
    fprintf(output_file,"%sNG/%i,%f\n",sps_list[sps].sps_name,datamatrix[conf].ind_number,datamatrix[conf].age);
 }}
close (output_file);
output_file = fopen ("class.out","w+");
for (s=0 ; s< nuspecs; s++){
  sps = s ;
  for (c =  0; c < sps_list[sps].num_confs ; c ++){
    conf =   sps_list[sps].conflist[c] ;
    fprintf(output_file,"%sNG/%i,%sNG\n",sps_list[sps].sps_name,datamatrix[conf].ind_number,sps_list[sps].sps_name);
       }
}
close (output_file);
}


give_gapped(int sps){
int c,l, conf;
output_file= fopen ("configs_g.tps","w");
 for (c= 0 ;c < sps_list[sps].num_confs; c ++){
   conf =   sps_list[sps].conflist[c] ;
   if (excl[sps][conf] == 1 ) continue;
   if (DIMS == 2 )
       fprintf(output_file,"LM=%i\n",LANDS);
   else
     fprintf(output_file,"LM3=%i\n",LANDS);
   for (l = 0 ; l < LANDS ; l ++){
     if (DIMS == 2 )
       fprintf(output_file,"%f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y);
     else
       fprintf(output_file,"%f %f %f\n",datamatrix[conf].pt[l].x,datamatrix[conf].pt[l].y,datamatrix[conf].pt[l].z);}
   fprintf(output_file,"ID=%sG/%i\n",sps_list[sps].sps_name,datamatrix[conf].ind_number);
 }
close (output_file);


output_file = fopen ("cova_G.out","w");
  for (c =  0; c < sps_list[sps].num_confs ; c ++){
    conf =   sps_list[sps].conflist[c] ;
    if (excl[sps][conf] == 1 ) continue;
    fprintf(output_file,"%sG/%i,%f\n",sps_list[sps].sps_name,datamatrix[conf].ind_number,datamatrix[conf].age);
       }
close (output_file);
output_file = fopen ("class_G.out","w");
  for (c =  0; c < sps_list[sps].num_confs ; c ++){
    conf =   sps_list[sps].conflist[c] ;
    if (excl[sps][conf] == 1 ) continue;
    fprintf(output_file,"%sG/%i,%sG\n",sps_list[sps].sps_name,datamatrix[conf].ind_number,sps_list[sps].sps_name);
       }
close (output_file);
}


sample_datamatrix (){
int i,j,c,s, guere, conf,  vanconf=0, espec, valor  ;


for ( s= 0 ;s < nuspecs; s ++){
  for (c= 0 ; c < bak_sps_list[s].num_confs; c ++){
   conf = bak_sps_list[s].conflist[c] ;
   if (( conf == bak_sps_list[s].confmaxage) || ( conf == bak_sps_list[s].confminage ) ){
      resam_datamatrix (conf,vanconf) ;
      vanconf ++ ;
     /* if (s == 1 )
         printf("%i,",conf); */
       }
    else
    {
    valor =  rand() % 100 ;
    if (valor > 30){ //30
      resam_datamatrix(conf,vanconf);
      vanconf++; }
      else
      {
     // printf(" %i=%i",s,conf);
      }
     }
  }
 }

 for (j = 0 ; j < nuspecs; j ++){
   guere = 0   ;
   for (i = 0 ; i < vanconf; i ++){
     if ( datamatrix[i].sp_number == bak_sps_list[j].sp_number){
           sps_list [j].conflist[guere] = i ;
           datamatrix[i].sp_number = j ;
           sps_list [j].sp_number = j ;
           guere ++ ;
          }
     sps_list [j].num_confs = guere ;}
   }
minmax_age_sp (nuspecs) ;

return (vanconf);
}


resam_datamatrix(int conf,int place){
int i;

datamatrix[place].age = back_mtx[conf].age;
datamatrix[place].std_sp_age = back_mtx[conf].std_sp_age;
datamatrix[place].sp_number = back_mtx[conf].sp_number ;
datamatrix[place].confnumber = back_mtx[conf].confnumber ;

datamatrix[place].nulands =back_mtx[conf].nulands ;
strcpy (datamatrix[place].sps_name,back_mtx[conf].sps_name) ;
strcpy (datamatrix[place].ind_number, back_mtx[conf].ind_number) ;
for ( i = 0 ; i < LANDS ; i ++ ){
  datamatrix[place].pt[i].x = back_mtx[conf].pt[i].x ;
  datamatrix[place].pt[i].y = back_mtx[conf].pt[i].y ;
  if (DIMS == 3)
   datamatrix[place].pt[i].z = back_mtx[conf].pt[i].z ; }
}

void give_consense(int sps){
double min , max , span , step, start, time ;
int a,l ;
 min = sps_list[sps].min_age ;
 max = sps_list[sps].max_age ;
 span = max - min ;
 step = span / CAT_INTER_AVG ;
 start = sps_list[sps].min_age + (step/2) ;

output_file = fopen ("cova_cons.out","w");
 for (a= 0 ; a < CAT_INTER_AVG ; a ++){
     time = start + step * a ;
     fprintf(output_file,"%s_Stg_%i,%f\n",sps_list[sps].sps_name,a,time);}
close (output_file);
output_file = fopen ("class_cons.out","w");
 for (a= 0 ; a < CAT_INTER_AVG ; a ++){
     time = start + step * a ;
     fprintf(output_file,"%s_Stg_%i,%s\n",sps_list[sps].sps_name,a,sps_list[sps].sps_name);}
close (output_file);

output_file = fopen ("consense.tps","w");
 for (a= 0 ; a < CAT_INTER_AVG ; a ++){
  if (DIMS == 2 )
       fprintf(output_file,"LM=%i\n",LANDS);
   else
     fprintf(output_file,"LM3=%i\n",LANDS);
   for (l = 0 ; l < LANDS ; l ++){
      if (DIMS == 2 )
        fprintf(output_file,"%f %f\n",consense_matrix[sps][a].pt[l].x,consense_matrix[sps][a].pt[l].y);
      else
       fprintf(output_file,"%f %f %f\n",consense_matrix[sps][a].pt[l].x,consense_matrix[sps][a].pt[l].y,consense_matrix[sps][a].pt[l].z);}
    fprintf(output_file,"ID=%s_Stg_%i\n",sps_list[sps].sps_name,a);}

close (output_file);
}

bak_minmaxage(){
int i ;
for (  i = 0 ;   i < nuspecs ; i ++ ) {
       bak_sps_list[i].confminage = sps_list[i].confminage ;
       bak_sps_list[i].confmaxage = sps_list[i].confmaxage ; }
}



void improve_map_changes (int resa) { // estoy modificando guich_map, transformations y branch_labels.  Transform_rnd y  guich_rnd
int n, d, e, nodo, r;
r = resa - 1 ;
for (n = 0 ; n <  nnods; n++){
  chg [n][1] = 0 ; chg [n][1] = 0 ;}

for ( n = 0 ; n < intnods ; n ++){
   nodo = optlist [n] ;
   d  = firs[nodo]  ;
   e  = sis [ d  ] ;
  if ( resa == 0 )
  {
   if ( easy_trans[d][0] > 0 &&  easy_trans[e][0] > 0 ){
       chg [d][0] = 1 ; chg[e][0] = 1 ; chg[nodo][0] = 1 ;
    if (easy_trans[d][0] > easy_trans[e][0] ){
        easy_trans[nodo][0] = easy_trans[nodo][0] + easy_trans[e][0] ;
        easy_trans[d][0] = easy_trans[d][0] - easy_trans[e][0] ;
        easy_trans[e][0] = 0 ; }
   if (easy_trans[d][0] < easy_trans[e][0] ){
        easy_trans[nodo][0] = easy_trans[nodo][0] + easy_trans[d][0] ;
        easy_trans[e][0] = easy_trans[e][0] - easy_trans[d][0] ;
        easy_trans[d][0] = 0 ; }
   if (easy_trans[d][0] == easy_trans[e][0] ){
       easy_trans[nodo][0] =  easy_trans[nodo][0] + easy_trans[d][0] ;
       easy_trans[e][0] = 0  ;
       easy_trans[d][0] = 0 ; }
   }
   if ( easy_trans[d][0] < 0 &&  easy_trans[e][0] < 0 ){
     chg [d][0] = 1 ; chg[e][0] = 1 ; chg [nodo][0] = 1 ;
    if (easy_trans[d][0] > easy_trans[e][0] ){
        easy_trans[nodo][0] = easy_trans[nodo][0] + easy_trans[d][0] ;
        easy_trans[e][0] = easy_trans[e][0] - easy_trans[d][0] ;
        easy_trans[d][0] = 0  ;   }
    if (easy_trans[d][0] < easy_trans[e][0] ){
        easy_trans[nodo][0] = easy_trans[nodo][0] + easy_trans[e][0] ;
        easy_trans[d][0] = easy_trans[d][0] - easy_trans[e][0] ;
        easy_trans[e][0] = 0 ; }
    if (easy_trans[d][0] == easy_trans[e][0] ){
       easy_trans[nodo][0] =  easy_trans[nodo][0] + easy_trans[d][0] ;
       easy_trans[e][0] = 0  ;
       easy_trans[d][0] = 0 ; }
   }
   if ( easy_trans[d][1] > 0 &&  easy_trans[e][1] > 0 ){
       chg [d][1] = 1 ; chg[e][1] = 1 ; chg [nodo][1] = 1 ;
    if (easy_trans[d][1] > easy_trans[e][1] ){
        easy_trans[nodo][1] = easy_trans[nodo][1] + easy_trans[e][1] ;
        easy_trans[d][1] = easy_trans[d][1] - easy_trans[e][1] ;
        easy_trans[e][1] = 0 ; }
   if (easy_trans[d][1] < easy_trans[e][1] ){
        easy_trans[nodo][1] = easy_trans[nodo][1] + easy_trans[d][1] ;
        easy_trans[e][1] = easy_trans[e][1] - easy_trans[d][1] ;
        easy_trans[d][1] = 0 ; }
   if (easy_trans[d][1] == easy_trans[e][1] ){
       easy_trans[nodo][1] =  easy_trans[nodo][1] + easy_trans[d][1] ;
       easy_trans[e][1] = 0  ;
       easy_trans[d][1] = 0 ; }
   }
   if ( easy_trans[d][1] < 0 &&  easy_trans[e][1] < 0 ){
     chg [d][1] = 1 ; chg[e][1] = 1 ; chg [nodo][1] = 1 ;
    if (easy_trans[d][1] > easy_trans[e][1] ){
        easy_trans[nodo][1] = easy_trans[nodo][1] + easy_trans[d][1] ;
        easy_trans[e][1] = easy_trans[e][1] - easy_trans[d][1] ;
        easy_trans[d][1] = 0  ;
        }
    if (easy_trans[d][1] < easy_trans[e][1] ){
        easy_trans[nodo][1] = easy_trans[nodo][1] + easy_trans[e][1] ;
        easy_trans[d][1] = easy_trans[d][1] - easy_trans[e][1] ;
        easy_trans[e][1] = 0 ; }
    if (easy_trans[d][1] == easy_trans[e][1] ){
       easy_trans[nodo][1] =  easy_trans[nodo][1] + easy_trans[d][1] ;
       easy_trans[e][1] = 0  ;
       easy_trans[d][1] = 0 ; }
     }
   }
  else
  {
   if ( easy_trans_rnd[resa][d][0] > 0 &&  easy_trans_rnd[resa][e][0] > 0 ){
       chg [d][0] = 1 ; chg[e][0] = 1 ; chg[nodo][0] = 1 ;
    if (easy_trans_rnd[resa][d][0] > easy_trans_rnd[resa][e][0] ){
        easy_trans_rnd[resa][nodo][0] = easy_trans_rnd[resa][nodo][0] + easy_trans_rnd[resa][e][0] ;
        easy_trans_rnd[resa][d][0] = easy_trans_rnd[resa][d][0] - easy_trans_rnd[resa][e][0] ;
        easy_trans_rnd[resa][e][0] = 0 ; }
   if (easy_trans_rnd[resa][d][0] < easy_trans_rnd[resa][e][0] ){
        easy_trans_rnd[resa][nodo][0] = easy_trans_rnd[resa][nodo][0] + easy_trans_rnd[resa][d][0] ;
        easy_trans_rnd[resa][e][0] = easy_trans_rnd[resa][e][0] - easy_trans_rnd[resa][d][0] ;
        easy_trans_rnd[resa][d][0] = 0 ; }
   if (easy_trans_rnd[resa][d][0] == easy_trans_rnd[resa][e][0] ){
       easy_trans_rnd[resa][nodo][0] =  easy_trans_rnd[resa][nodo][0] + easy_trans_rnd[resa][d][0] ;
       easy_trans_rnd[resa][e][0] = 0  ;
       easy_trans_rnd[resa][d][0] = 0 ; }
   }
   if ( easy_trans_rnd[resa][d][0] < 0 &&  easy_trans_rnd[resa][e][0] < 0 ){
     chg [d][0] = 1 ; chg[e][0] = 1 ; chg [nodo][0] = 1 ;
    if (easy_trans_rnd[resa][d][0] > easy_trans_rnd[resa][e][0] ){
        easy_trans_rnd[resa][nodo][0] = easy_trans_rnd[resa][nodo][0] + easy_trans_rnd[resa][d][0] ;
        easy_trans_rnd[resa][e][0] = easy_trans_rnd[resa][e][0] - easy_trans_rnd[resa][d][0] ;
        easy_trans_rnd[resa][d][0] = 0  ;   }
    if (easy_trans_rnd[resa][d][0] < easy_trans_rnd[resa][e][0] ){
        easy_trans_rnd[resa][nodo][0] = easy_trans_rnd[resa][nodo][0] + easy_trans_rnd[resa][e][0] ;
        easy_trans_rnd[resa][d][0] = easy_trans_rnd[resa][d][0] - easy_trans_rnd[resa][e][0] ;
        easy_trans_rnd[resa][e][0] = 0 ; }
    if (easy_trans_rnd[resa][d][0] == easy_trans_rnd[resa][e][0] ){
       easy_trans_rnd[resa][nodo][0] =  easy_trans_rnd[resa][nodo][0] + easy_trans_rnd[resa][d][0] ;
       easy_trans_rnd[resa][e][0] = 0  ;
       easy_trans_rnd[resa][d][0] = 0 ; }
   }
   if ( easy_trans_rnd[resa][d][1] > 0 &&  easy_trans_rnd[resa][e][1] > 0 ){
       chg [d][1] = 1 ; chg[e][1] = 1 ; chg [nodo][1] = 1 ;
    if (easy_trans_rnd[resa][d][1] > easy_trans_rnd[resa][e][1] ){
        easy_trans_rnd[resa][nodo][1] = easy_trans_rnd[resa][nodo][1] + easy_trans_rnd[resa][e][1] ;
        easy_trans_rnd[resa][d][1] = easy_trans_rnd[resa][d][1] - easy_trans_rnd[resa][e][1] ;
        easy_trans_rnd[resa][e][1] = 0 ; }
   if (easy_trans_rnd[resa][d][1] < easy_trans_rnd[resa][e][1] ){
        easy_trans_rnd[resa][nodo][1] = easy_trans_rnd[resa][nodo][1] + easy_trans_rnd[resa][d][1] ;
        easy_trans_rnd[resa][e][1] = easy_trans_rnd[resa][e][1] - easy_trans_rnd[resa][d][1] ;
        easy_trans_rnd[resa][d][1] = 0 ; }
   if (easy_trans_rnd[resa][d][1] == easy_trans_rnd[resa][e][1] ){
       easy_trans_rnd[resa][nodo][1] =  easy_trans_rnd[resa][nodo][1] + easy_trans_rnd[resa][d][1] ;
       easy_trans_rnd[resa][e][1] = 0  ;
       easy_trans_rnd[resa][d][1] = 0 ; }
   }
   if ( easy_trans_rnd[resa][d][1] < 0 &&  easy_trans_rnd[resa][e][1] < 0 ){
     chg [d][1] = 1 ; chg[e][1] = 1 ; chg [nodo][1] = 1 ;
    if (easy_trans_rnd[resa][d][1] > easy_trans_rnd[resa][e][1] ){
        easy_trans_rnd[resa][nodo][1] = easy_trans_rnd[resa][nodo][1] + easy_trans_rnd[resa][d][1] ;
        easy_trans_rnd[resa][e][1] = easy_trans_rnd[resa][e][1] - easy_trans_rnd[resa][d][1] ;
        easy_trans_rnd[resa][d][1] = 0  ;
        }
    if (easy_trans_rnd[resa][d][1] < easy_trans_rnd[resa][e][1] ){
        easy_trans_rnd[resa][nodo][1] = easy_trans_rnd[resa][nodo][1] + easy_trans_rnd[resa][e][1] ;
        easy_trans_rnd[resa][d][1] = easy_trans_rnd[resa][d][1] - easy_trans_rnd[resa][e][1] ;
        easy_trans_rnd[resa][e][1] = 0 ; }
    if (easy_trans_rnd[resa][d][1] == easy_trans_rnd[resa][e][1] ){
       easy_trans_rnd[resa][nodo][1] =  easy_trans_rnd[resa][nodo][1] + easy_trans_rnd[resa][d][1] ;
       easy_trans_rnd[resa][e][1] = 0  ;
       easy_trans_rnd[resa][d][1] = 0 ; }
     }
   }

}

} //improve_map



make_ttags (int up) {
double max_sup, min_sup, half, red,green,pace,blue, * pt_lim;
int i;
char etiqueta [300] ;
max_sup = -9999 ;
min_sup = 9999 ;
if (up)
 pt_lim = &sup_limit_cont[0] ;
else
 pt_lim = &inf_limit_cont[0] ;

 for (i = 0 ; i < nnods ; i++){
 if  (pt_lim[i] > max_sup )
   max_sup = pt_lim[i] ;
 if  (pt_lim[i] < min_sup )
   min_sup = pt_lim[i] ; }
half = (max_sup - min_sup)/2 ;
pace = 255 / half  ;

if (blue_red){
 for (i = 0 ; i < nnods ; i++){
  if ( pt_lim[i] < (min_sup + half) ){
   etiqueta [0] = NULL;
   red = (( (min_sup + half) - pt_lim[i] ) * pace ); // 255 - (( (min_sup + half) - pt_lim[i] ) * pace );
   //blue   = 255 ;
   sprintf(etiqueta,"(%i,0,0)/",(int)red);
   color_labels[i][0] = '\0';
   strcpy(color_labels[i],etiqueta);
   }
  else{
   etiqueta [0] = NULL;
   blue  = ((pt_lim[i] - (min_sup + half) ) * pace ); //255 - ((pt_lim[i] - (min_sup + half) ) * pace );
   //red   = 255 ;
   sprintf(etiqueta,"(0,0,%i)/",(int) blue); //sprintf(etiqueta,"(%i,0,%i)/",(int)red,(int) blue);
   color_labels[i][0] = '\0';
   strcpy(color_labels[i],etiqueta);  }
 }
}
else{
	 for (i = 0 ; i < nnods ; i++){
	 if  (pt_lim[i] > max_sup )
	   max_sup = pt_lim[i] ;
	 if  (pt_lim[i] < min_sup )
	   min_sup = pt_lim[i] ; }
	half = (max_sup - min_sup)/2 ;
	pace = 255 / half  ;
	 for (i = 0 ; i < nnods ; i++){
	  if ( pt_lim[i] < (min_sup + half) ){
	   red = 255 ;
	   etiqueta [0] = NULL;
	   green = (pt_lim[i] - min_sup ) * pace ;
	   sprintf(etiqueta,"(%i,%i,0)/",(int)red,(int) green);
	   color_labels[i][0] = '\0';
	   strcpy(color_labels[i],etiqueta);
	   }
	  else{
	      etiqueta [0] = NULL;
	   green = 255 ;
	   red =   255 - (pt_lim[i] - (min_sup + half) ) * pace ;
	   sprintf(etiqueta,"(%i,%i,0)/",(int)red,(int) green);
	   color_labels[i][0] = '\0';
	   strcpy(color_labels[i],etiqueta);  }
 }  }
}

void check_monotonicity (int nuca ) {
int i, k,s,l ,ya ;
double  firs, last,var1,var2;
Punktyp * pt1 ;
Punktyp * pt2 ;

 for (s =  0; s < nuspecs ; s ++){
  ya = 0 ;
  printf("\nEspecie %s\n",sps_list[s].sps_name);
  for (i =  0; i < (nuca-1) ; i ++)
    printf("Stg_%i,",i);
  printf("\n");
  for (k =  0; k < (nuca-1) ; k ++){ //  for (k =  0; k < (nuca-1) ; k ++){
    //pt1 = consense_matrix[ s ][ nuca-1 ].pt ; //pt1 = consense_matrix[ s ][ 0 ].pt ;
    pt2 = consense_matrix[ s ][k ].pt ;
    //var1 =  pair_conf_dist (pt1, pt2) ;
   printf ("\nSTG_%i=,",k);
   for (l = 0  ; l < nuca ; l ++){ // for (l = k -1 ; l > 0 ; l --){  //for (l = k + 1 ; l < nuca ; l ++)
     if (k == l )
     printf("-,");
     else{
     //pt2 = consense_matrix[ s ][l ].pt ;
     pt1 = consense_matrix[ s ][l ].pt ;
     var2 =  pair_conf_dist (pt1, pt2) ;
      printf ("%f,",var2);
     }
     /*if (var2 < var1 ) {
       if (!ya){
       printf("\nWarning. Shape does not change monotonically with time in species %i (%s)",s,sps_list[s].sps_name);
       printf("\n   Shape for stage %i is more similar to stage %i, than stage %i (%f/%f)",l,nuca,k,var1,var2 );
       ya ++ ;
       }
       else
         printf("\n   Shape for stage 0 is more similar to shape of stage %i than to stage %i (%f/%f)",l,k,var1,var2 );*/
      }

    }}
}

