/*
 Copyright 2018 Raffaele Marino
 
 This file is part of BSP (BackTracking Survey Propagation).
 
 BSP is free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.
 
 BSP is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.
 
 You should have received a copy of the GNU General Public License
 along with BSP; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/

                                /*COPYRIGHTS OF random.h: GIORGIO PARISI*/
                                        /*VERSION C++  01/01/2003*/


/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/
/****************************************************************************************************************/



typedef unsigned long long RANDOM_TYPE;
typedef unsigned  long random_type;
#define MASSIMO_RAND     2147483647L 
#define MASSIMO_RAND_MEZZI     1073741824L
#define MRAND  myrand = (16807L * myrand) % 2147483647L;
#define FRAND  MRAND frand = (float)myrand * inv_massimo_rand;
#ifdef  MAIN
RANDOM_TYPE myrand;
random_type yourrand;
float inv_massimo_rand = 1.0 / (float)MASSIMO_RAND;
float inv_massimo_rand_mezzi = 1.0 / (float)MASSIMO_RAND_MEZZI;
float frand;
int lrand;
#else
extern RANDOM_TYPE myrand;
extern random_type yourrand;
extern float inv_massimo_rand;
extern float inv_massimo_rand_mezzi ;
extern float frand;
extern int lrand;
#endif
#define LRAND(range) FRAND lrand=(int)(frand*(float)range);if(lrand==range){lrand--;}

#define YOUR_MASSIMO_RAND 4294967295

#define YOURRAND     yourrand = ((1664525L * yourrand) + 1013904223L) ;//&YOUR_MASSIMO_RAND;
inline unsigned long long int Random(){FRAND return myrand;}


