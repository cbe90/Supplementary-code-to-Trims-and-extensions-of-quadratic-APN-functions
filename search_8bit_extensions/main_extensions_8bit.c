/* Compile with: g++ -O2 -march=native -funroll-loops main_extensions_8bit.c -o extensions_8bit
Authors: C. Beierle, G. Leander, L. Perrin  -- 2021

This program randomly searches for quadratic 8-bit APN functions that can be obtained as an extension of a quadratic 7-bit APN function.
*/

#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <stdio.h>
#include <time.h>
#include <random>
#include "prefixes7.h" // The list of quadratic 7-bit APN functions

#define  N 8 // dimension of the function to find
#define RE_SHUFFLE 100000 // iterations after which the random state is re-shuffled

#define hw(x) __builtin_popcount(x)

// the following three lines are needed for the degree bound
#define DEGREE 2 // we only search for functions with algebraic degree less than or equal to 2
int cube_ctr[(1<<N)];
int cube_sum[(1<<N)];

// to track the running time
time_t runtime;

// the linear function on the upper half of the APN to be constructed
int L[N-1];

// contains the random initial state
int P[N-1][(1<<N)];
int r[(1<<N)];

// to check differential properties of the upper half of the APN
int betas[(1<<(N-1))][(1<<(N-2))];
int possibles[(1<<(N-1))][1<<(N)];

int solutions;
long long iterations;
int proceed;

int sbox[(1<<N)]; // it stores the (partial) S-box that we are going to construct (undefined values represented by -1)
int sbox_DDT[(1<<N)][(1<<N)]; // it stores the (partial) DDT of sbox

// random number generators to generate integers uniformly in [0,(1<<N))
std::random_device rd;
std::mt19937_64 gen(rd());
std::uniform_int_distribution<int> dis(0,(1<<(N))-1);
std::uniform_int_distribution<int> dis2(0,1);
std::uniform_int_distribution<int> dis3(0,N_PREFIXES-1); // to choose a random 7-bit APN on the lower half

// applys the Fisher-Yates shuffle to the array arr to get a uniform permutation
void shuffle_array(int* arr) {
    uint32_t j = 0;
    uint32_t tmp = 0;
    for (int i=(1<<(N))-1; i!=0; i--) {
        decltype(dis.param()) nrange (0, i);
        dis.param(nrange);
        j = dis(gen);
        // swap
        tmp = arr[j];
        arr[j] = arr[i];
        arr[i] = tmp;
    }
}

void printArray2(int A[1<<N]) {
	printf("{0x%02x",A[0]);
	for (int i=1;i<(1<<N);i++)
		printf(",0x%02x",A[i]);
	printf("};\n");
}

void fprintArray2(FILE *fp, int A[1<<N]) {
	fprintf(fp, "{0x%02x",A[0]);
	for (int i=1;i<(1<<N);i++)
		fprintf(fp, ",0x%02x",A[i]);
	fprintf(fp, "};\n");
}

// checks if $c \preceq x$
int is_prec(int c, int x) {
  return ((c & x) == c);
}

int addDDTInformation_lower(int c) {
  for (int d=0;d<c;d++) {
    if ((hw(c^d)&0x1)==0) {
      sbox_DDT[c^d][sbox[c]^sbox[d]]+=2;
      if (sbox_DDT[c^d][sbox[c]^sbox[d]]>2) return 0;
    }
  }
  return 1;
}

int removeDDTInformation_lower(int c) {
  for (int d=0;d<c;d++) {
    if ((hw(c^d)&0x1)==0) {
      sbox_DDT[c^d][sbox[c]^sbox[d]]-=2;
      if (sbox_DDT[c^d][sbox[c]^sbox[d]]==2) return 0;
    }
  }
  return 1;
}

// here, we only consider differences with msb=1
int addDDTInformation_upper(int c) {
  for (int d=(1<<(N-1));d<c;d++) {
    if ((hw(c^d)&0x1)==0) {
      sbox_DDT[c^d][sbox[c]^sbox[d]]+=2;
      if (sbox_DDT[c^d][sbox[c]^sbox[d]]>2) return 0;
    }
  }
  return 1;
}

// here, we only consider differences with msb=1
int removeDDTInformation_upper(int c) {
  for (int d=(1<<(N-1));d<c;d++) {
    if ((hw(c^d)&0x1)==0) {
      sbox_DDT[c^d][sbox[c]^sbox[d]]-=2;
      if (sbox_DDT[c^d][sbox[c]^sbox[d]]==2) return 0;
    }
  }
  return 1;
}

int addDegreeInformation(int c) {
  for (int u=0; u<(1<<N); u++) {
    if (hw(u)>=(DEGREE+1) && is_prec(c,u)) {
      cube_ctr[u]++;
      cube_sum[u] = cube_sum[u]^sbox[c];
      if (cube_ctr[u] == (1<<hw(u))) {
        // if the sum over the cube is 0, the degree must be higher
        if (cube_sum[u]!=0) return 0;
      }
    }
  }
  return 1;
}

int removeDegreeInformation(int c) {
  for (int u=0; u<(1<<N); u++) {
    if (hw(u)>=(DEGREE+1) && is_prec(c,u)) {
      cube_ctr[u]--;
      cube_sum[u] = cube_sum[u]^sbox[c];
      if (cube_ctr[u] == (1<<hw(u))-1) {
        if (cube_sum[u]!=sbox[c]) return 0;
      }
    }
  }
  return 1;
}

int addPoint_lower(int c) {
    return addDegreeInformation(c);
}

void removePoint_lower(int c) {
    removeDegreeInformation(c);
}

int addPoint_upper(int c) {
  return (addDDTInformation_upper(c));
}

void removePoint_upper(int c) {
    removeDDTInformation_upper(c);
}

// returns L(x)
int eval_lin(int x) {
  int y = 0;
  for (int i=0;i<(N-1);i++) {
    if ((x>>i)&(0x1)) {
      y = y^L[i];
    }
  }
  return y;
}

int is_possible_difference(int a, int b) {
  for (int x=0; x<(1<<(N-1)); x++) {
    if (((sbox[x])^(sbox[x^a]))==b) return 1;
  }
  return 0;
}

// after the lower half of the APN is fixed, extract all possible output differences for any input difference a
void extract_betas() {
  int ct;
  for (int a=1;a<(1<<(N-1));a++) {
    ct = 0;
    for (int j=0; j<(1<<(N)); j++)
    {
      if (is_possible_difference(a,j)) {
        betas[a][ct]=j;
        ct++;
      }
    }
  }
}

// L[a] must be different from betas[a][b1]^betas[a][b2]
void remove_impossibles() {
  for (int a=1; a<(1<<(N-1));a++) {
    for (int b1=0; b1<(1<<(N-2)); b1++) {
      for (int b2=0; b2<(1<<(N-2)); b2++) {
        possibles[a][betas[a][b1]^betas[a][b2]] = 0;
      }
    }
  }
}

// recursive construction of the sbox.
void nextValue_first_half(int nr, int depth) {
	int y;

	if (depth==((1<<(N-1))-1)) {
    proceed = 0;
		return;
	}

	//not complete
	int x=depth+1;	// get next free position in the look-up table
	for (int z=0;z<2;z++) {
    if (proceed) {
		y = z^r[depth]; // fix random last coordinate
			sbox[x]=prefixes[nr][x]^(y<<(N-1));
			if (!addPoint_lower(x)) goto UNDO;

      if (proceed) nextValue_first_half(nr, depth+1);

			//undo the changes
			UNDO:
			if (proceed)
      { removePoint_lower(x);
			sbox[x]=-1;}
    }
	}
}

int is_potential_L(int d, int y) {
  int x, xS, yS;
  x = (1<<d);
  L[d] = y;
  xS = x;
  yS = L[d];
  for (int l=x;l<(x<<1)-1;l++) {
    if (possibles[xS][yS]==0) {L[d]=-1; return 0;}
    xS = xS+1;
    yS = eval_lin(xS);
  }
  if (possibles[xS][yS]==0) {L[d]=-1; return 0;}
  return 1;
}

// recursive construction of the sbox.
void nextValue_second_half(int nr, int depth, char* filename) {
	int y,xS,yS;
	iterations++;

  if (iterations>=RE_SHUFFLE) { // display the status every RE_SHUFFLE seconds
		 proceed = 0;
	}

	//complete
	if (depth==(N-1)) {
			solutions++;
			printf("found a new apn extension for APN function no. %d: #%d\n",nr,solutions);
			printArray2(sbox);
      printf("\n");
			fflush(stdout);
			FILE *fp = fopen(filename, "a");
			if (fp == NULL)
            {
                printf("Error opening file!\n");
		fflush(stdout);
            }
            else
            {
                fprintArray2(fp, sbox);
            }
            fclose(fp);
            proceed = 0;
		return;
	}

	//not complete
	int x=(1<<depth);  // new base point
	for (int z=0;z<(1<<N);z++) {   // y represents L(x)
    y = P[depth][z]; // fix random y for L
    if (is_potential_L(depth,y)) { // if TRUE, this function sets L[depth] to y
    xS = x;
    yS = L[depth];
		for (int l=x;l<(x<<1)-1;l++) {
			sbox[(1<<(N-1))+xS]=(yS^(sbox[xS])); // set sbox to L(x)+prefix(x)

			if (!addPoint_upper((1<<(N-1))+xS)) goto UNDO_SECOND; // undo if it can't be apn
      xS = xS+1;
      yS = eval_lin(xS);
    }
    sbox[(1<<(N-1))+xS]=(yS^(sbox[xS])); // set sbox to L(x)+prefix(x)

    if (!addPoint_upper((1<<(N-1))+xS)) goto UNDO_SECOND; // undo if it can't be apn

    if (proceed) nextValue_second_half(nr, depth+1, filename);

			//undo the changes in reverse order
			UNDO_SECOND:
      do {
			     removePoint_upper((1<<(N-1))+xS);
			     sbox[(1<<(N-1))+xS]=-1;
           xS = xS-1;
      } while (xS != (x-1));
      L[depth]=-1;
    }
	}
}

void search(char* filename, int max_runtime) {
    solutions=0;
    int ctr = 0;
    int nr;
    FILE *fp = fopen(filename, "w");
    if (fp == NULL)
    {
            printf("Error opening file!\n");
    }
    fclose(fp);

    // initialize P
		for (int t=0;t<N-1;t++) {
		 for (int x=0;x<(1<<(N));x++) {
	      P[t][x] = x;
		 }
	 }

	 while(time(NULL)-runtime < max_runtime) {
      ctr++;
	     memset(cube_ctr,0,(1<<N)*sizeof(int));
	     memset(cube_sum,0,(1<<N)*sizeof(int));
       nr = dis3(gen);  // fix a random 7-bit APN for lower half
	     for (int x=0;x<(1<<N);x++) {
					 sbox[x]=-1;
           r[x] = dis2(gen); // generate random state to fix last coordinate
			 }

        // the 7-bit APNs all have sbox[0]=0
	      sbox[0] = 0;
	      if (!addPoint_lower(0)) exit(0);

			 // shuffle the state
			 for (int t=0;t<N-1;t++) {
					shuffle_array(P[t]);
		   }

			 // fix the lower half
			 proceed = 1;
			 nextValue_first_half(nr,0);
       // done fixing lower half

       // initializations for constructing upper half
       iterations = 0;
       memset(sbox_DDT,0,(1<<N)*(1<<N)*sizeof(int));
       for (int x=0;x<(N-1);x++) {
           L[x]=-1;
       }
       for (int t=0; t<(1<<(N-1)); t++) {
         for (int k=0;k<(1<<N);k++) {
           possibles[t][k] = 1;
         }
       }
       extract_betas();
       remove_impossibles();

       sbox[1<<(N-1)] = (sbox[0]);
       if (!addPoint_upper(1<<(N-1))) exit(0);

       // try to construct the upper half
       proceed = 1;
       nextValue_second_half(nr,0,filename);
       // done after RE_SHUFFLE iterations

       if ((ctr%100)==0) {
           printf("tests so far:%d \n",ctr);
           printf("solutions so far:%d \n",solutions);
   		     printf("running time: %li sec\n\n", time(NULL)-runtime);
           fflush(stdout);
        }
	}
}

int main(int argc, char* argv[])
{
		if (argc != 3) {
	        	printf("Usage: %s <outfile> <max_runtime in seconds> ...\n", argv[0]);
	        	return -1;
	    	}
		srand (time(NULL));
		runtime = time(NULL);

		search(argv[1],atoi(argv[2]));
		printf("\nFinished. Total solutions: %d. Total running time: %li sec\n", solutions, time(NULL)-runtime);
		exit(0);
}
