//******************************************************************************
// Diffuse.cpp Copyright(c) 2003 Jonathan D. Lettvin, All Rights Reserved.
//******************************************************************************
// Permission to use this code if and only if the first eight lines are first.
// This code is offered under the GPL.
// Please send improvements to the author: jdl@alum.mit.edu
// The User is responsible for errors.
//******************************************************************************
// Compilation:
// g++ \
//     -I/usr/include/SDL \
//     -I/usr/local/include/SDL
//     -I/usr/local/include/boost
//     -I/home/jdl/Desktop/install/boost-trunk
//     -Wall
//     -o diffuse
//     diffuse.cpp
//     -lSDL
//     -lSDL_ttf
//     -lboost_program_options
//******************************************************************************
//  "Usage: %s {Number} [{Jiggle}]\n"
//  "  Number: count of points to distribute over unit sphere\n"
//  "  Jiggle: lower limit of largest movement below which relaxation stops\n"
//  "Fix one charged point at (1,0,0) on a unit sphere.\n"
//  "Randomly distribute additional charged points over unit sphere.\n"
//  "Prevent identical positioning.\n"
//  "Apply formula for charge repulsion to calculate movement vector.\n"
//  "After all movement vectors have been calculated, apply to charges.\n"
//  "Normalize resulting vectors to constrain movement to sphere.\n"
//  "Repeat until movement falls below limit, or rounds rises above limit."
//  "Output as a C static double array of coordinate triples."
//******************************************************************************
// Overview:
// Diffuse a number of points to an approximately stationary position using
// the standard physics formula for charge repulsion (inverse square law)
// over the surface of a sphere.  For vertex counts equalling platonic solids,
// the result will be a distribution approximating that platonic solid.
// Otherwise, distributions are sufficiently random to make
// every possible great circle cross the same number of edges,
// give or take a small variation.
// Use the first point as an anchor at (1,0,0) then randomly distribute points.
// Precautions are taken to avoid identical points (a zerodivide, or "pole").
// The expected area of an inscribed circle around any point should converge to
// the area of the sphere divided by the number of points, therefore the radius
// of said circle should be approximately linear with 1/sqrt(N).  This program
// arbitrarily uses the default minimum incremental movement value .03/sqrt(N).
//******************************************************************************
// Charges in foreground are shown twice as bright as those in background.
//******************************************************************************
// OVERALL SEQUENCE OF OPERATION:
// ----
// main: Sequence of operations:
// 1) gather, constrain, and default command-line arguments
// 2) construct "points" object (vector of spherically constrained coordinates)
// 3) output the coordinates calculated during construction
// 4) quit
// ----
// 2: sequence of operations
// a) Initialize random number generator
// b) construct vector of coordinates fixing the first and randomizing others
// c) relax the vector (cause point-charge forces to push points apart)
// d) calculate nearest neighbor for all points and record that minimum radius
// ----
// 2b: sequence of operations
// e) push (1,0,0) on vector
// f) push random normalized coordinates on vector, pop if another is identical
// g) push slot for per-coordinate minimum radius
// ----
// 2c: sequence of operations
// h) for every point get inverse-square increment from all other points
// i) zero the force on the (1,0,0) point to keep anchor
// j) after acquiring all increments, sum and normalize increments, and apply
// k) repeat until maximum movement falls below a minimum
// ----
// 2be and 2bf: sequence of operations
// l) construct either the (1,0,0) point or a random point
// m) normalize to place the point on the unit sphere
// ----
// 2ch: sequence of operations
// n) calculate distance between indexed point and a specific other point
// o) take inverse square of distance
// p) add directly to increment coordinates
// ----
// 2cj: sequence of operations
// q) keep a copy of the starting coordinates for the point
// r) add increment to move point, and normalize it back onto the sphere
// s) calculate distance to starting coordinates and
// t) remember largest movement on surface of sphere
// ----
// 3: sequence of operations
// u) output all point coordinates as a C style static double array
//******************************************************************************
#include <iostream>  // sync_with_stdio
#include <fstream>   // Output file
#include <sstream>   // Caption
#include <cstdio>    // printf
#include <cstdlib>   // I believe sqrt is in here
#include <ctime>     // Used to salt the random number generator
#include <cmath>     // Various mathematical needs
#include <complex>   // Screen Coordinates
#include <string>    // Output filename
#include <vector>    // Used to contain many points
#include <valarray>  // Used to implement a true XYZ vector

#include <boost/format.hpp>
#include <boost/program_options.hpp>
#include <SDL/SDL.h>
#include <SDL/SDL_ttf.h>
//******************************************************************************

using namespace std; // Necessary to gain access to many C++ names
using namespace boost;

char *Program;
size_t Number=0;            // Cause point count to have a failing value.
size_t Species=0;           // Choose the number of species
double Jiggle;              // Stop relaxation when movement drops below.
bool   Limit=false;
string Output="";

//******************************************************************************
typedef valarray<double>coordinates; // To simplify declarations

TTF_Font* loadfont(char* file, int ptsize) {
  TTF_Font* tmpfont;
  tmpfont = TTF_OpenFont(file, ptsize);
  if (tmpfont == NULL){
    boost::format why( "Can't loadfont %1% because: %2%" );
    throw( ( why % file % TTF_GetError( ) ).str( ) );
  }
  return tmpfont;
}

enum textquality {solid, shaded, blended};
 
void drawtext(
  TTF_Font *fonttodraw,
  SDL_Surface **destsurf,
  char fgR, char fgG, char fgB, char fgA, 
  char bgR, char bgG, char bgB, char bgA,
  char text[],
  textquality quality)
{
  SDL_Color tmpfontcolor = {fgR,fgG,fgB,fgA};
  SDL_Color tmpfontbgcolor = {bgR, bgG, bgB, bgA};
  if (quality == solid)
    *destsurf =
      TTF_RenderText_Solid(fonttodraw, text, tmpfontcolor);
  else if (quality == shaded)
    *destsurf =
      TTF_RenderText_Shaded(fonttodraw, text, tmpfontcolor, tmpfontbgcolor);
  else if (quality == blended)
    *destsurf =
      TTF_RenderText_Blended(fonttodraw, text, tmpfontcolor);
} 

//******************************************************************************
class XYZ { // This class contains operations for placing and moving points
  private:
    static const size_t N=3;
    double change_magnitude;
    coordinates xyz;   // This holds the coordinates of the point.
    coordinates dxyz;  // This holds the summed force vectors from other points
    coordinates exyz;  // This holds the summed potential energy
    coordinates jxyz;  // This holds the jiggle
    double minimum;
    inline double random() { return(double((rand()%1000)-500)); } // ordinates
    inline double square(const double& n) { return(n*n); }
    inline coordinates square(const coordinates& n) { return(n*n); }
    inline double inverse(const double& n) { return(1.0/n); }
    XYZ& inverse_square() { xyz*=inverse(square(magnitude())); return *this; }
    inline double magnitude() { return(sqrt((xyz*xyz).sum())); }
    void normalize() { xyz/=magnitude(); } // unit vector
    void limit() { double mag=magnitude(); if(mag>1.0) xyz/=mag; }
  public:
    XYZ(): xyz(N), dxyz(N) {
      xyz[0]=random(); xyz[1]=random(); xyz[2]=random(); minimum=2.0; normalize();
      if(Limit) {
        double r=double( ( rand() % 10 ) + 1 );
        double sqr = sqrt( r );
        xyz[0]/=sqr; xyz[1]/=sqr; xyz[2]/=sqr;
      }
    }
    XYZ(const double& x,const double& y,const double& z) : xyz(N), dxyz(N) {
      xyz[0]=x; xyz[1]=y; xyz[2]=z; minimum=2.0;
    }
    XYZ(const coordinates& p) : xyz(N), dxyz(N) {
      xyz=p; minimum=2.0;
    }
    ~XYZ() { }
    coordinates& array() { return xyz; }
    inline double &X() { return xyz[0]; }
    inline double &Y() { return xyz[1]; }
    inline double &Z() { return xyz[2]; }
    inline double &R() { return minimum; }
    void zero_force() { dxyz=0.0; exyz=0.0; }
    void zero_jiggle() { jxyz=0.0; }
    double change() { return(change_magnitude); }
    double magnitude(XYZ& b) { // Return length of vector.  (not const)
      return(sqrt( square(b.array()-xyz).sum() ));
    }
    void sum_force(XYZ& b) { // Cause force from each point to sum.  (not const)
      dxyz+=(XYZ(b.array()-xyz).inverse_square().array()); // Calculate and add
      // exyz is supposed to sum the square root of each force vector
    }
    void add_jiggle( ) {
      for( size_t i=0; i<3; ++i )
        jxyz[0] = Jiggle * double( ( rand( ) % 21 ) - 10 )/10;
        jxyz[1] = Jiggle * double( ( rand( ) % 21 ) - 10 )/10;
        jxyz[2] = Jiggle * double( ( rand( ) % 21 ) - 10 )/10;
    }
    void move_over_sphere() { // Cause point to move due to force
      coordinates before=xyz;                       // Save previous position
      xyz-=dxyz;                                    // Follow movement vector
      xyz+=jxyz;                                    // Brownian motion
      if(Limit) limit();                            // Contain within sphere
      else normalize();                             // Project back to sphere
      before-=xyz;                                  // Calculate traversal
      change_magnitude=sqrt((before*before).sum()); // Record largest
    }
    void report(const double& d) {
      printf("  { %+1.3e,%+1.3e,%+1.3e,%+1.3e }",xyz[0],xyz[1],xyz[2],d);
    }
    void report() {
      printf("  { %+1.3e,%+1.3e,%+1.3e }",xyz[0],xyz[1],xyz[2]);
    }
    void objfile() {
      const double offset=0.0;
      printf("v %+1.3e %+1.3e %+1.3e",xyz[0],xyz[1],xyz[2]+offset);
    }
    void objfile( ofstream &ofs ) {
      const double offset=0.0;
      boost::format v( "v %1$+1.3e %2$+1.3e %3$+1.3e # %4$+1.3e" );
      ofs <<
        (
          v %
          xyz[0] %
          xyz[1] %
          ( xyz[2]+offset ) %
          magnitude()
        ).str( ) <<
        endl;
    }
};

//******************************************************************************
typedef struct {
      Uint32 color;
      Uint32 charge;
      double shell;
      string name;
} propertyt;

class Point { // This class organizes properties of a point charge
  private:
    XYZ xyz_;
    size_t species_;
    static const propertyt property[ 5 ];
  public:
    enum { Sodium, Potassium, Calcium, Chlorine, Protein, Count };
    Point( const size_t species = Sodium );
    ~Point( );

    inline Point & init( const size_t species = Sodium );
    inline XYZ &xyz( ) { return xyz_; }
    inline Uint32 color( ) { return property[ species_ ].color; }
    inline Uint32 charge( ) { return property[ species_ ].charge; }
    inline double shell( ) { return property[ species_ ].shell; }
    inline string name( ) { return property[ species_ ].name; }
};

const propertyt Point::property[ 5 ] = {
  { 0xFFFFFF, +1, +2, "Sodium" },
  { 0x00FF00, +1, +1, "Potassium" },
  { 0x0000FF, +2, +3, "Calcium" },
  { 0xFFFF00, -1, +1, "Chlorine" },
  { 0xFF0000, -1, +9, "Protein" }
};

Point::Point( const size_t species ) : species_( species )
{
}

Point::~Point( )
{
}

Point &Point::init( const size_t species ) 
{
  species_ = species;
  return *this;
}

//******************************************************************************
class Points { // This class organizes expression of relations between points
  private:
    const size_t N;   // Number of point charges on surface of sphere
    const double L;   // Threshold of movement below which to stop
    char        *S;   // Name of this vertex set
    size_t rounds;    // Index of rounds processed
    vector<XYZ>V;     // List of point charges
    vector<Uint32>C;  // List of point color
    vector<Sint32>Z;  // List of point charge value
    vector<Point>P;
    double maximum_change; // The distance traversed by the most moved point
    double minimum_radius; // The radius of the smallest circle
    time_t T0;        // Timing values
    vector< pair< string, Uint32 > > species;

    //**************************************************************************
    // Cause all points to sum forces from all other points
    void relax1( const size_t Count ) {
      vector< XYZ >::iterator a, b;
      size_t an, bn;
      for(an = 0, a = V.begin( ); an < Count && a != V.end( ); ++an, ++a ) {
        a->zero_force( );
        for( bn = 0, b = V.begin( ); bn < Count && b != V.end( ); ++bn, ++b ) {
          if( b != a ) a->sum_force( *b );
        }
      }
      for(an = 0, a = V.begin( ); an < Count && a != V.end( ); ++an, ++a )
        a->move_over_sphere( );
    }

    inline double dR( coordinates& a, coordinates& b ) {
      double dX = b[ 0 ] - a[ 0 ];
      double dY = b[ 1 ] - a[ 1 ];
      double dZ = b[ 2 ] - a[ 2 ];
      return sqrt( dX*dX + dY*dY + dZ*dZ );
    }

    inline double dR( XYZ& a, XYZ& b ) {
      double dX = b.X( ) - a.X( );
      double dY = b.Y( ) - a.Y( );
      double dZ = b.Z( ) - a.Z( );
      return sqrt( dX*dX + dY*dY + dZ*dZ );
    }

  public:

    //**************************************************************************
    Points(char *s,const size_t& n,const double& l) :
      N(n), L(l)
    {
      S=s;
      T0=time(0L);                   // Get the current time
      srand(T0);                     // Salt the random number generator.
      species.push_back( pair< string, Uint32 >( "Na", 0xFFFFFF ) );
      species.push_back( pair< string, Uint32 >(  "K", 0x00FF00 ) );
      species.push_back( pair< string, Uint32 >( "Ca", 0x0000FF ) );
      species.push_back( pair< string, Uint32 >( "Cl", 0x00FFFF ) );
      species.push_back( pair< string, Uint32 >( "Pr", 0xFF0000 ) );
      V.push_back(XYZ(1.0,0.0,0.0)); // Create Anchored first point V[0] (1,0,0)
      C.push_back(0xFF0000);
      P.push_back( Point( ) );  // New mechanism about to replace old
      while(V.size()<N) {   // For all other points, until we have enough
	V.push_back(XYZ()); // Create randomized position
        C.push_back( species[(rand()% Species)].second );
        P.push_back( Point( ) );
	coordinates& last=V.back().array(); // Remember this position
	for(size_t i=V.size()-1;i--;) { // And check to see if it is occupied
	  coordinates& temp=V[i].array();
          if( dR( temp, last ) < 0.001 ) { // Arbitrary minimum
	    V.pop_back(); // Remove the position if it is already occupied
	    break;
	  }
	}
      }
    }

    //**************************************************************************
    ~Points() {}

    //**************************************************************************
    time_t dt( ) { return time( 0L ) - T0; }

    //**************************************************************************
    void relax( const size_t Count ) {
      relax1( Count );
    }

    //**************************************************************************
    complex<double> minmax( const size_t Count ) {
      size_t i, j;
      minimum_radius=1.0; // On a unit sphere, the maximum circle radius is 1.0
      maximum_change=0.0;
      vector< XYZ >::iterator a, b;
      for( i=0, a = V.begin( ); i < Count && a != V.end( ); ++i, ++a ) {
        for( j=0, b = V.begin( ); j < Count && b != V.end( ); ++j, ++b ) {
          if( a == b ) continue;
          double rtemp=a->magnitude( *b )/2.0;
          if(rtemp<minimum_radius) minimum_radius=rtemp; // Record when smaller.
          if(rtemp<a->R( )) a->R( )=rtemp;
        }
        if(a->change()>maximum_change) maximum_change=a->change();
      }
      return complex<double>( minimum_radius, maximum_change );
    }

    //**************************************************************************
    const size_t count( ) { return N; }

    //**************************************************************************
    coordinates& operator[](const size_t& i) { // Caller access to positions
      return(V[i].array());
    }

    //**************************************************************************
    Uint32 operator()(const size_t& i) { // Caller access to positions
      return(C[i]);
    }

    //**************************************************************************
    void report() { // Output run statistics and positions of all points
#if 1
#if 0
      printf("// Elapsed time=%ld seconds\n",1L+time(0L)-T0);
      printf("#ifndef CLASS_COMPOUND_SURFACE\n#define CLASS_COMPOUND_SURFACE\n");
      printf("class compound_surface {\n");
      printf("  private:\n");
      printf("    static const double XYZ[%d][3];\n",N);
      printf("    static const size_t Points;\n");
      printf("  public:\n");
      printf("    compound_surface() {}\n");
      printf("    ~compound_surface() {}\n");
      printf("}; // class compound_surface\n");
      printf("const size_t compound_surface::Points=%d;\n",N);
      printf("const double compound_surface::XYZ[%d][3]={\n",N);
      V[0].report();
      for(size_t i=1;i<N;i++) { printf(",\n"); V[i].report(); }
      printf("\n};\n");
      printf("#endif // CLASS_COMPOUND_SURFACE\n");
#else
      if( Output == string( "" ) ) {
        //puts("g sphere");
        //V[0].objfile();
        //for(size_t i=1;i<N;i++) { printf("\n"); V[i].objfile(); }
        //printf("\nf 1 2 3\n");
      } else {
        ofstream ofs( Output.c_str( ) );
        if( ofs ) {
          ofs << "g diffuse" << endl;
          V[0].objfile( ofs );
          for(size_t i=1;i<N;i++) V[i].objfile( ofs );
          ofs << "f 1 2 3" << endl;
        }
      }

#endif
#else
      printf(
	  "/* Rounds   =%d/%d */\n"
	  "/* Jiggle dV=%+1.2e/%+1.2e */\n"
	  "/* minimum r=%+1.2e */\n"
	  "/* elapsed time<=%ld seconds. */\n"
	  "static size_t Points_%s=%d;\n"
	  "static double vertex_%s[%d][4] = {\n"
	  "/*{  X         , Y         , Z         , Rmin       } */\n"
	  ,
	  rounds,R,maximum_change,L,minimum_radius,1L+time(0L)-T0,S,N,S,N);
	  "static size_t Points_%s=%d;\n"
	  "static double vertex_%s[%d][4] = {\n"
	  "/*{  X         , Y         , Z         , Rmin       } */\n"
	  ,
	  rounds,R,maximum_change,L,minimum_radius,1L+time(0L)-T0,S,N,S,N);
      V[0].report(V[0].R( ));
      for(size_t i=1;i<N;i++) { printf(",\n"); V[i].report(V[i].R( )); }
      printf("\n};\n");
#endif
    }
};

//******************************************************************************
class Display {
  public:
    typedef complex< Uint16 > UXY;
    typedef complex< int > XY;
    Display( Points &p, const size_t mode = 0 );
    ~Display( );
    void show1( const XY &position, const Uint32 color );
    void show2( const XY &position, const Uint32 color );
    void show3( const XY &position, const Uint32 color );
    void show4( const XY &position, const Uint32 color );
    void (Display::*show)( const XY &position, const Uint32 color );
    void operator( )( );
  protected:
  private:
    Points &p_;
    vector< UXY > modes_;
    XY xy0;
    size_t mode_;
    size_t back_;
    int scalar_;
    SDL_Surface *video_;
    TTF_Font *font_;
    Uint32 colors_[ 256 ];
    valarray<double> Euler;
    inline size_t index( const XY xy, const size_t n ) {
      int x = xy.real( ) + xy0.real( );
      int y = xy.imag( ) + xy0.imag( );
      return size_t( n * ( y * modes_[ mode_ ].real( ) + x ) );
    }
    inline Uint8 *base( const XY xy, const size_t n ) {
      return ((Uint8 *)video_->pixels) + index( xy, n );
    }
};

//******************************************************************************
Display::Display( Points &p, const size_t mode ) :
  p_( p ), mode_( mode ), Euler(3)
{
  modes_.push_back( UXY( 659, 659 ) );
  modes_.push_back( UXY( 329, 329 ) ); ///< 5x5 65x65 panels with 1 pixel sep.
  modes_.push_back( UXY( 320, 240 ) );
  modes_.push_back( UXY( 640, 480 ) );

  if( modes_.size( ) <= mode_ ) {
    boost::format why( "Illegal mode %1%" );
    throw( ( why % mode_ ).str( ) );
  }
  xy0 = XY(
            int( modes_[ mode_ ].real( ) ) / 2,
            int( modes_[ mode_ ].real( ) ) / 2 );
  /// Reduce the diameter from 100% to 80% of the display window
  scalar_ = xy0.real( );
  if( xy0.imag( ) < scalar_ ) scalar_ = xy0.imag( );
  scalar_ = ( scalar_ * 8 ) / 10;

  if( -1 == TTF_Init( ) ) {
    boost::format why( "Can't TTF_Init because: %1%" );
    throw( ( why % TTF_GetError( ) ).str( ) );
  }

  if( NULL == 
    ( font_ =
      loadfont( (char *)"/usr/share/fonts/truetype/freefont/FreeSerif.ttf", 10 ) ) )
    {
      boost::format why( "Can't loadfont FreeSerif.ttf" );
      throw( ( why ).str( ) );
  }

  if( 0 > SDL_Init( SDL_INIT_VIDEO ) ) {
    boost::format why( "Can't SDL_Init because: %1%" );
    throw( ( why % SDL_GetError( ) ).str( ) );
  }
  atexit( SDL_Quit );
  atexit( TTF_Quit );
  //atexit( free_font );
  Uint32 surface = 0;
  surface |= SDL_SWSURFACE; /// HW or SW
  surface |= SDL_DOUBLEBUF;
  //surface |= SDL_FULLSCREEN;
  //if( NULL == ( video_ = SDL_SetVideoMode( 640, 480, 0, surface ) ) )
  if( NULL ==
      ( video_ =
        SDL_SetVideoMode(
        modes_[mode_].real( ),
        modes_[mode_].imag( ),
        0,
        surface ) ) )
  {
    boost::format why( "Can't SDL_SetVideoMode because: %1%" );
    throw( ( why % SDL_GetError( ) ).str( ) );
  }
  SDL_Color palette[ 256 ];
  size_t i;
  for( i = 0; i < 256; ++i ) {
    palette[i].r = i;
    palette[i].g = i;
    palette[i].b = i;
  }
  SDL_SetColors( video_, palette, 0, 256 );
  for( i = 0; i < 256; ++i ) {
    colors_[ i ] = SDL_MapRGB( video_->format, i, i, i );
  }
  switch( video_->format->BytesPerPixel ) {
    case 1: show = &Display::show1; break;
    case 2: show = &Display::show2; break;
    case 3: show = &Display::show3; break;
    case 4: show = &Display::show4; break;
    default:
      boost::format why( "BytesPerPixel: %1%, must be between 1 and 4." );
      throw( ( why % video_->format->BytesPerPixel ).str( ) );
      break;
  }
  back_ = 0x00;
  SDL_FillRect( video_, NULL, colors_[ back_ ] );
  /* Accept only keyboard events */
  for ( i = 0; i<SDL_NUMEVENTS; ++i ) {
    if ( (i != SDL_KEYDOWN) && (i != SDL_QUIT) ) {
      SDL_EventState(i, SDL_IGNORE);
    }
  }
  //Jiggle = 0.3;
}

//******************************************************************************
Display::~Display( ) {
}

//******************************************************************************
void Display::show1( const XY &position, const Uint32 color ) {
  *base( position, 1 ) = Uint8( color );
}

//******************************************************************************
void Display::show2( const XY &position, const Uint32 color ) {
  *(Uint16 *)base( position, 2 ) = Uint16( color );
}

//******************************************************************************
void Display::show3( const XY &position, const Uint32 color ) {
  int reverse = ( SDL_BYTEORDER == SDL_BIG_ENDIAN );
  Uint8 *src = (Uint8 *)&color, *tgt = base( position, 3 ) + 2*reverse;
  if( reverse ) { *tgt-- = *src++; *tgt-- = *src++; *tgt = *src; }
  else          { *tgt++ = *src++; *tgt++ = *src++; *tgt = *src; }
}

//******************************************************************************
void Display::show4( const XY &position, const Uint32 color ) {
  *(Uint32 *)base( position, 4 ) = color;
}

//******************************************************************************
void Display::operator( )( ) {
  size_t round = 0, n, N = p_.count( ), Count = N;
  complex<double> minmax;
  double angle = 0.0;
  time_t t0=time( 0L ), t1;
  SDL_Event event;
  bool running = true;
  size_t D = 32;

  SDL_EnableKeyRepeat( SDL_DEFAULT_REPEAT_DELAY, SDL_DEFAULT_REPEAT_INTERVAL );

  while( running ) {
    if( 0 != SDL_PollEvent( &event ) ) {
      switch( event.type ) {
        case SDL_KEYDOWN:
          switch( event.key.keysym.sym ) {
            case SDLK_q: case SDLK_ESCAPE: running = false; continue; break;
            case SDLK_PAGEUP:   Count += D*int((Count+D) <= N); break;
            case SDLK_PAGEDOWN: Count -= D*int( Count    >  D); break;
            case SDLK_UP:       Count +=   int( Count    <  N); break;
            case SDLK_DOWN:     Count -=   int( Count    >  1); break;
            default: break;
          }
          break;
      }
    }
    angle = double( round ) * 6.28/ 360.0;

    /// Try to own the surface.
    if ( SDL_MUSTLOCK( video_ ) && ( 0 > SDL_LockSurface( video_ ) ) ) continue;
 
    /// Surface is now owned within the enclosing braces.
    else {

      /// Put all the points on the surface.
      for( n=0; n < Count; ++n ) {
        const coordinates &xyz = p_[ n ];
        double x = xyz[ 0 ], y = xyz[ 1 ], z = xyz[ 2 ];
        x *= double( scalar_ );
        y *= double( scalar_ );
        z *= double( scalar_ );
        int X = int( x ), Y = int( y );
        XY xyt( X, Y );

        Uint32 color = p_( n );
#if 1
        const double dim = 64.0;
        double zt = dim + ( 255.0 - dim ) * 0.5 * ( xyz[ 2 ] + 1.0 );
        color &= 0x010101;
        color *= Uint32( zt );
#else
        if( xyz[ 2 ] < 0 ) color &= 0x777777;   // lower the intensity
#endif

        (this->*show)( xyt, color );
      }

      ++round;

      t1 = time( 0L );
      if( ( t1 != t0 ) || !(round&0xFF) ) {
        t0 = t1;
#if 0
        stringstream caption;
        caption << round << ' ' << minmax.real( ) << ' ' << minmax.imag( );
        SDL_WM_SetCaption( caption.str( ).c_str( ), 0 );
#else
        // boost::format caption( "%1% %2% %4% %5$e %6$e" );
        boost::format caption( "N = %1% round = %2% minR = %3% maxdR = %4% t = %5%" );
        SDL_WM_SetCaption(
            (
             caption
             // % "" // Program
             // % Number
             // % Jiggle
             % Count
             % round
             % minmax.real( )
             % minmax.imag( )
             % p_.dt( )
            ).str( ).c_str( ), 0 );
#endif
      }

      //SDL_Color fontColor = { 255, 255, 255, 0 };
      //video_ = TTF_RenderText_Solid( font_, "DIFFUSE", fontColor );

      /// Give up ownsership of the surface.
      if ( SDL_MUSTLOCK( video_ ) ) SDL_UnlockSurface( video_ );
    }

    /// Update entire screen
    SDL_UpdateRect( video_, 0, 0, 0, 0 );

    /// Black out all the points on the surface.
    for( n=0; n < N; ++n ) {
      const coordinates &xyz = p_[ n ];
      double x = xyz[ 0 ], y = xyz[ 1 ], z = xyz[ 2 ];
      x *= double( scalar_ );
      y *= double( scalar_ );
      z *= double( scalar_ );
      int X = int( x ), Y = int( y );
      XY xyt( X, Y );
      (this->*show)( xyt, colors_[ back_ ] );
    }

    /// Adjust positions for all points.
    /// NOTE: This is done OUTSIDE the scope of surface lock.
    /// This operator updates positions for all the points.
    p_.relax( Count );
    minmax = p_.minmax( Count );

  }
}


//******************************************************************************
int main(int argc,char **argv) {
  Program = argv[ 0 ];
  stringstream ss;
  boost::format error( "Error: (%1%) %2%" );

  try {
    ios::sync_with_stdio(true);

    namespace po = boost::program_options;
    po::variables_map vm;

    po::options_description cmdline_options( "Command line options" );
    cmdline_options.add_options()
      ("help,h",                      "this help message")
      ("jiggle,j",po::value<double>( &Jiggle)->default_value(0.003),"Brownian")
      ("limit,l", po::value<  bool>( &Limit )->default_value( true),"Contain")
      ("number,n",po::value<size_t>( &Number)->default_value(  100),"charges")
      ("species,s",po::value<size_t>( &Species)->default_value(  1),"species")
      ("output,o",po::value<string>( &Output)->default_value(   ""),"filename");
    po::options_description desc( "diffuse (redistribute charges on a sphere)" );
    desc.add( cmdline_options);

    /// Parse command-line
    po::store(po::command_line_parser(argc,argv).options(desc).run(), vm);
    po::notify( vm );

    if( vm.count( "help" ) ) {
      cout << desc << endl;
      throw( "help requested" );
    }

    if( Number <= 1 ) throw( "1 < Number not true" );
    double j = 1.00/sqrt(double(Number));
    if( !vm.count( "jiggle" ) ) Jiggle = j;

    boost::format jbad( "0 < Jiggle < %1% not true" );
    if( Jiggle <= 0.0 || Jiggle > j ) throw( ( jbad % j ).str( ) );

    boost::format sbad( "0 < Species < %1% not true" );
    if( Species < 1 || Species > 5 ) throw( ( sbad % Species ).str( ) );

    Points P((char *)"default",Number,Jiggle);
    // P can now be addressed for specific XYZ values for scaling and reporting
    // For instance P[0] should return a valarray& of three elements (1,0,0)
    // In this program, the array is simply output as a C static double array

    Display display( P, 1 );

    display( );

    P.report();
  }
  catch( const string &s ) {
    ss << ( error % "string" % s ).str( ) << endl;
  }
  catch( const char * &s ) {
    ss << ( error % "char *" % s ).str( ) << endl;
  }
  catch( ... ) {
    ss << ( error % "default" % "unknown" ).str( ) << endl;
  }
  cerr << ss.str( );
  return ss.str( ).length( );
}
//******************************************************************************
// End of file
//******************************************************************************
