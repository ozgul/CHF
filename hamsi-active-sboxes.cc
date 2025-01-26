// Cryptanalysis of round 2 SHA3 candidate Hamsi
// Original code by Christophe De Canniere and Ozgul Kucuk
// Commented by Vesselin Velichkov, 20090903
#include <cstdlib>
#include <iostream>

using namespace std;

#define ROTL32(v, n) (((v) << (n)) | ((v) >> (32 - (n))))

// the L transformation of Hamsi
inline void Mix(uint32_t* a,uint32_t* b,uint32_t* c,uint32_t* d) {
	  *a = ROTL32(*a,13);
	  *c = ROTL32(*c,3);
	  *b ^= *a ^ *c;
	  *d ^= *c ^ (*a<<3);

	  *b = ROTL32(*b,1);
	  *d = ROTL32(*d,7);
	  *a ^= *b ^ *d;
	  *c ^= *d ^ (*b<<7);

	  *a = ROTL32(*a,5);
	  *c = ROTL32(*c,22);
}

#define L Mix

#define S(r,c) &s[r * 4 + c]

// Hamsi diffusion layer
inline void diffuse256(uint32_t s[16]) {
	  // const int line=4;
	  L(S(0,0),S(1,1),S(2,2),S(3,3));
	  L(S(0,1),S(1,2),S(2,3),S(3,0));
	  L(S(0,2),S(1,3),S(2,0),S(3,1));
	  L(S(0,3),S(1,0),S(2,1),S(3,2));
}

// r is the state matrix. it is composed of 16 words of 32 bits each 16x32=512
// pos is the column index of a 32 bit word
// bit is a value of one bit: 0/1, vpv
void eliminate(uint32_t* r[512], int& rows, int pos, uint32_t bit)
{
	  // cycle over all rows
	  for (int i = 0; i < rows; ++i)
			 // if word[i][pos] and bit are both 1
			 if ((r[i][pos] & bit) != 0)
			 {
					// cycle over the rest of the rows
					for (int j = i + 1; j < rows; ++j)
						  // if another bit in the colum is 1 - eliminate it
						  if ((r[j][pos] & bit) != 0)
								 // xor row j with row i
								 for (int c = 0; c < 32; ++c)
										r[j][c] ^= r[i][c];

					// put the i-th row at the bottom
					swap(r[i], r[--rows]);

					break;
			 }
}

// compute the Hamming weight of a 32-bit word 
int weight(uint32_t x)
{
	  x = x - ((x >> 1) & 0x55555555);                
	  x = (x & 0x33333333) + ((x >> 2) & 0x33333333); 

	  return
			 (((x + (x >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

// compute the total weight of one row of the left submatrix 
// and of one row of the right submatrix
int weight(uint32_t* r)
{
	  int w = 0;

	  // side=0/1 selects the left (0) or the right (1) submatrix
	  // in one row of one submatrix we have 16 32-bit words
	  // ordered by 4. every 4 words represent one row of the 4x4
	  // state of Hamsi. c selects one of the 4 lists of 4 32-bit words:
	  // c=0: 0 1 2 3 | c=1: 4 5 6 7 | c=2: 8 9 10 11 | c=3: 12 13 14 15
	  // eg. if side=0 and c=1 then r[side * 16 + c] == r[1] will be
	  // the 1-st 32-bit word of the left submatrix
	  // and r[side * 16 + c +  4] == r[1 + 4] will be the 5-th 32-bit word;
	  // we do c, c+4, c+8, c+12 because Hamsi sboxes are applied like this:
	  // sbox[0,4,8,12], sbox[1,5,9,13], sbox[2,6,10,14], sbox[3,7,11,15]
	  for (int side = 0; side < 2; ++side)
			 for (int c = 0; c < 4; ++c)
					// count the total weight of one row of the left submatrix 
					// (side=0, 16 32-bit words) and of one row of the right
					// submatrix (side=1, 16 32-bit words)
					w += weight(r[side * 16 + c     ] | // 32 bits
									r[side * 16 + c +  4] | // 32 bits
									r[side * 16 + c +  8] | // 32 bits
									r[side * 16 + c + 12]); // 32 bits

	  return w;
}

// r[512] is a matrix of 512 rows and (16+16) columns of 32-bit elements
// the first 16 columns of r define the left submatrix (input to Hamsi)
// the second 16 columns define the right submatrix (output from Hamsi)
void find_active(uint32_t* r[512], int rows, uint32_t active[8])
{
	  // side=0/1 selects the left (0) or the right (1) submatrix
	  for (int side = 0; side < 2; ++side)
	       // c=0: 0 1 2 3 | c=1: 4 5 6 7 | c=2: 8 9 10 11 | c=3: 12 13 14 15
			 for (int c = 0; c < 4; ++c)
			 {
					// active is an arrey of 4+4 32-bit words
					// the left 4 and the right 4 32-bit words
					// store the number of active sboxes in 
					// the left and the right submatrices of r respectively.
					// left is input, right is output to/from Hamsi transformation.
					// The state of Hamsi is represented as a 4x4 array of 32-bit 
               // words. This arrey has 4*32=128 columns each of which 
					// contain 4 bits. To every column one sbox is applied.
					// In total we have 128 sboxes per Hamsi state. So we have
					// 128 inputs and 128 outputs which is equal to 4+4 32-bit
					// words.These 4+4 32-bit words are stored in active[].
					// Whenever in active[] a bit is set to 1 it means that
					// the corresponding sbox is active (ie. has non-zero
					// difference). remember that the Hamsi sboxes are applied like this:
					// sbox[0,4,8,12], sbox[1,5,9,13], sbox[2,6,10,14], sbox[3,7,11,15]
					// this is why we do c, c+4, c+8, c+12 next
					active[side * 4 + c] = 0;
					for (int i = 0; i < rows; ++i)
						  // this is a bit-sliced count of 32 sboxes at a time
						  // c=0 selects 32 sboxes from words 0,4,8,12. c=1
						  // selects 32 sboxes from words 1,5,9,13, etc.
						  // the Hamming weight of active will give us the total
						  // number of active sboxes
						  active[side * 4 + c] |= 
								 r[i][side * 16 + c     ] |
								 r[i][side * 16 + c +  4] |
								 r[i][side * 16 + c +  8] |
								 r[i][side * 16 + c + 12];
			 }
}

void print(uint32_t* r)
{
	  printf("%d\n", weight(r));

	  for (int i = 0; i < 32; ++i)
	  {
			 printf("%08X ", r[i]);

			 if ((i % 4) == 3)
					printf("\n");
      
			 if ((i % 16) == 15)
					printf("\n");
	  }
}

const int rounds = 4;

int main()
{
	  // 
	  // diffuse_m is an array with three dimensions:
	  // 
	  // (1) number of rounds (first dimension)
	  // (2) each round has a state of 512 bits so there are 512
	  //     basis vectors, they form the rows of the matrix
	  //     (second dimension)
	  // (3) the matrix has 32 columns (16+16). each column is composed of 
	  //     32-bit elements. the first 16 columns represent the identity
	  //     matrix. it has size 512x512 bits (16 cols * 32 bits = 512 bits)
	  //     the second 16 columns represent the 512-bit state of Hamsi.
	  //     
	  // For one round, (2) and (3) define a matrix of size 512x(32*(16 + 16))
	  // of 32-bit elements:
	  //
	  // left submatrix 512x512| right submatrix 512x512
	  // 
	  // 1000...512 cols...000 | 1000...512 cols...000
	  // 0100...512 cols...000 | 0100...512 cols...000
	  // 0010...512 cols...000 | 0010...512 cols...000
	  // 
	  //                ... 512 rows ...
	  // 
	  // 0000...512 cols...001 | 0000...512 cols...001
	  // 
	  uint32_t diffuse_m[rounds - 1][512][16 + 16] = {{{0}}};
	  // an array of row pointers (same as diffuse_m)
	  uint32_t* diffuse_r[rounds - 1][512];

	  // cycle over rounds
	  // and fill the left amd right submatrices
	  for (int s = 0; s < rounds - 1; ++s)
	  {
			 // copy pointers to rows 
			 for (int i = 0; i < 512; ++i) 
					diffuse_r[s][i] = diffuse_m[s][i];
  
			 for (int i = 0; i < 512; ++i)
			 {
					// i goes over the 512 rows; i / 32 counts the 32-bit words
					// within one row eg.for rows 0..31 we take word 1
					// for rows 32..63 we take word 2 etc. for row 480..511
					// we take word 16
					// with 1 << (i % 32) we successively set to 1 the bits 
               // within one word at positions 0..31
					// we do the above for the left and for the right 
					// submatrices

					// initialize the left submatrix to the identity matrix
					diffuse_r[s][i][i / 32     ] = 1 << (i % 32);
					// initialize the right submatrix to the identity matrix
					diffuse_r[s][i][i / 32 + 16] = 1 << (i % 32);

					// basically the left submatrix contains all 
					// possible 512-bit inputs to the Hamsi transform
					// while the right submatrix contains the resulting 
					// outputs. below we fill the right submatrix with valid
					// outputs from the Hamsi transform applying diffuse256()

					// apply Hamsi diffuse to the right submatrix
					diffuse256(diffuse_r[s][i] + 16);
			 }
	  }

	  //int lowest = (rounds - 1) * 512 + 1; // ? vpv
  
	  while (true)
	  {
			 // number of rows for every round
			 int rows[rounds - 1];
      
			 for (int s = 0; s < rounds - 1; ++s)
					rows[s] = 512;   // store number of rows for every round

			 while (true)
			 {
					// arrey which stores number of active sboxes for every
					// round. for one round we have 128 sboxes which have
               // 4*32 inputs and 4*32 outputs. this is why 
               // active[] has 8 elements per round (row)
					uint32_t active[rounds - 1][8];

					// store the number of active sboxes for every round
					for (int s = 0; s < rounds - 1; ++s)
						  find_active(diffuse_r[s], rows[s], active[s]);

					int rnd;
					int c;
					int side = 0;
					uint32_t bit = 0;

					// cycle over rounds
					for (rnd = 1; rnd < rounds - 1; ++rnd)
					{
						  // cycle over 4 columns of 32-bit words
						  for (c = 0; c < 4; ++c)
						  {
								 // active[rnd - 1][4 + c] is the input to round 'rnd'
								 // active[rnd][c] is the output from round 'rnd'
								 // (and input to round rnd+1)
								 // we xor the inputs and the outputs
								 // of 32 sboxes. by "inputs" and "outputs" we
								 // mean here 32 bit words which indicate
								 // weather we have a non-zero input or output 
								 // difference to an sbox. if a bit in the bit
								 // string of active[] is 1 then it means
								 // we have two different inputs/outputs of
								 // an sbox. if the bit is 0 then the inputs/outputs
								 // are the same. normally a zero input difference
								 // should result in a zero output difference and
								 // a non-zero input difference should result in a 
								 // non-zero output difference. therefore 
								 // we expect that the xor of the two active[]
								 // strings stored in bit to be equal to 0.
								 // if it is not zero then we have an inconsistency
								 // which we'll try to eliminate later
								 bit = active[rnd - 1][4 + c] ^ active[rnd][c];
		  
								 // if the exor is non-zero (bit != 0) then we have
								 // an inconsitency ie. there exist some sbox/es
								 // for which a non-zero input difference
								 // results in a zero output difference
								 // or vice versa. this is not possible
								 // so we try to eliminate those cases.
								 if (bit != 0)
								 {
										// find out at which bit position/s
										// the inconsistency resides. after the next
										// operation 'bit' will have 1-s only at the
										// position/s of the inconsistencies.
										bit &= ~(bit - 1);

										// next try to find where is the inconsitency
										// ie. weather we have non-zero input
										// differnce (the inconsistency is in round
										// 'rnd - 1') or we have a non-zero output
										// difference (the inconsistency is in 
										// round 'rnd')

										// if the output (active[rnd][c]) AND-ed
										// with the inconsitency string bit
										// gives 0 then the inconsistency
										// must be in round 'rnd-1' so
										// set rnd = rnd - 1
										if ((active[rnd][c] & bit) == 0)
										{
											  rnd = rnd - 1;
											  side = 1;
										}
		      
										//printf("eliminating inconsistency\n");
										// break from the inner for() loop
										break;
								 }
						  }
	      
						  // if there was an inconsistency then break
						  // from the outer for() loop
						  if (bit != 0)
								 break;
					}

					// if inconsistency was not found then
					// choose random columns within either the left
					// or the right submatrices and perform
					// Gaussian elimination on them using eliminate()
					// this operation is equivalent to lowering
					// the number of active sboxes in Hamsi
					if (bit == 0)
					{
						  bool stop = true;

						  // why is the next necessary?, vpv
						  for (int s = 0; s < rounds - 1; ++s)
								 if (rows[s] > 1)
										stop = false;

						  // why is the next necessary?, vpv
						  if (stop)
						  {
								 for (int s = 0; s < rounds - 1; ++s)
										print(diffuse_r[s][0]);

								 printf("----\n");

								 break;
						  }

						  // choose a random round
						  rnd  = random() % (rounds - 1);
						  // choose a random 32-bit column of the 4x4 Hamsi state
						  // c= 0, 1, 2, 3
						  // for example if c = 1 then the sbox will be applied
						  // on words c, c+4, c+8, c+12 ie. words 1, 5, 9, 13
						  // of the Hamsi state
						  c    = random() % 4;
						  // choose randomly the left (side=0) or the 
                    // right (size=1) submatrix
						  side = random() % 2;
						  // choose randomly a bit position
						  bit  = 1 << (random() % 32);

						  //printf("eliminating random sbox\n");
					}

					//printf("%d %d %d %08X\n", rnd, c, side, bit);

					// next eliminate one column of the matrix
					// if there was an inconcistency above then we'll
					// eliminate next the column with the inconsistency.
					// if there was no inconsistency then we'll eliminate
					// a random column
					eliminate(diffuse_r[rnd], rows[rnd], side * 16 + c     , bit);
					eliminate(diffuse_r[rnd], rows[rnd], side * 16 + c +  4, bit);
					eliminate(diffuse_r[rnd], rows[rnd], side * 16 + c +  8, bit);
					eliminate(diffuse_r[rnd], rows[rnd], side * 16 + c + 12, bit);
					/*
					  for (int s = 0; s < rounds - 1; ++s)
					  printf("%d ", rows[s]);

					  printf("\n");
					*/
					bool stop = false;

					// why?, vpv
					for (int s = 0; s < rounds - 1; ++s)
						  if (rows[s] == 0)
								 stop = true;

					if (stop)
						  break;
			 }
	  }
 
	  return 0;
}
