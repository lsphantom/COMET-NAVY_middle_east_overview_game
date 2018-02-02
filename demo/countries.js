var canvas,context,ocanvas,ocontext;
var m_countries;
var m_pixelsPerLonDegree,m_negpixelsPerLonRadian,m_bitmapOrigo,m_ww;
var m_group,m_s=1.0,m_x=1800,m_y=1300,m_level,m_index,m_ws=1.0;
var m_numnames,m_start,m_time,m_finished,m_errors;
var m_names=new Array();
var mx=0,my=0,mpress=false,mrelease=false;
var m_place,m_namesize="9";
var m_demo,m_showscores,m_showall,m_vol=0.2;
var cheat=0;
var m_scores;

/* programmed by Kevin Pickell, 2010 */
/* LimeGreenuced map data set was derived from data at http://www.naturalearthdata.com/about/terms-of-use/ */

/* group,scale,translatex,translatey,fontsize,country list */
var g_regions=[
	/* show all */
	0,0.17,0,0,"9","*",
	/* view scores */
	0,0.17,0,0,"9","*",
	/* provinces of Canada */
	2,0.55,150,400,"11","*",
	/* states of the USA */
	1,0.86,400,1200,"9","*",
	/* Europe */
	0,1.0,1800,1200,"9","Albania,Andorra,Austria,Belarus,Belgium,Bosnia & Herzegovina,Bulgaria,Croatia,Cyprus,Czech Republic,Denmark,Estonia,France,Germany,Gibraltar,Greece,Guernsey & Jersey,Hungary,Ireland,Isle of Man,Italy,Latvia,Liechtenstein,Lithuania,Luxembourg,Macedonia,Malta,Moldova,Netherlands,Poland,Portugal,Romania,San Marino,Monaco,Slovakia,Slovenia,Spain,Switzerland,Turkey,Ukraine,United Kingdom,Vatican City,Serbia,Montenegro,Kosovo,Northern Cyprus,Russia",
	/* Scandanavia */
	0,1.02,1800,900,"12","Aland,Denmark,Estonia,Faroe Islands,Finland,Iceland,Latvia,Lithuania,Norway,Russia,Sweden",
	/* North Africa */
	0,0.91,1670,1440,"11","Algeria,Benin,Burkina Faso,Cameroon,Central African Republic,Chad,Cote D'Ivoire,Djibouti,Egypt,Eritrea,Ethiopia,The Gambia,Ghana,Guinea,Guinea-Bissau,Liberia,Libya,Mali,Mauritania,Morocco,Niger,Nigeria,Senegal,Sierra Leone,Somalia,Somaliland,Sudan,Togo,Tunisia,Western Sahara",
	/* South and Central Africa */
	0,0.93,1860,1860,"11","Angola,Botswana,Burundi,Comoros,Congo,D.R. of Congo,Equatorial Guinea,Gabon,Kenya,Madagascar,Malawi,Mauritius,Mozambique,Namibia,Reunion,Rwanda,Sao Tome & Principe,Seychelles,South Africa,Lesotho,Swaziland,Tanzania,Uganda,Zambia,Zimbabwe",
	/* Middle East */
	0,0.985,2290,1560,"9","Afghanistan,Bahrain,Djibouti,Ethiopia,Eritrea,Iran,Iraq,Israel,Jordan,Kuwait,Lebanon,Oman,Palestine,Pakistan,Qatar,Saudi Arabia,Syria,Somalia,United Arab Emirates,Yemen",
	/* Asia */
	0,0.52,1410,740,"11","Ashmore And Cartier Islands,Australia,Bangladesh,Bhutan,British Indian Ocean Terr.,Brunei,Cambodia,China,Christmas Island,Cocos (Keeling) Islands,Federated States Of Micronesia,Hong Kong,India,Indonesia,Japan,North Korea,Guam,South Korea,Laos,Malaysia,Maldives,Mongolia,Myanmar,Nepal,Papua New Guinea,Northern Mariana Islands,Palau,Philippines,Singapore,Solomon Islands,Sri Lanka,Taiwan,Thailand,Timor Leste,Vietnam",
	/* Carribean */
	0,4.0,4800,7250,"12","Anguilla,Antigua & Barbuda,Aruba,Barbados,British Virgin Islands,Dominica,Dominican Republic,Grenada,Guadeloupe,Haiti,Martinique,Montserrat,Netherlands Antilles,Puerto Rico,St. Barthelemy,St. Kitts & Nevis,St. Lucia,St. Martin,St. Vincent & the Grenadines,Trinidad & Tobago,US Virgin Islands",
	/* Central America */
	0,2.0,1830,3540,"12","The Bahamas,Belize,Cayman Islands,Costa Rica,Cuba,Dominican Republic,El Salvador,Guatemala,Haiti,Honduras,Jamaica,Mexico,Nicaragua,Panama,Turks & Caicos Islands",
	/* South America */
	0,0.48,200,920,"11","Argentina,Bolivia,Brazil,Chile,Colombia,Ecuador,Falkland Islands,French Guiana,Guyana,Paraguay,Peru,Pitcairn Islands,South Georgia And The Sandwich Islands,Suriname,Uruguay,Venezuela",
	/* North America */
	0,0.37,0,260,"15","Canada,United States,Mexico",
	/* South Pacific */
	0,1,-330,1900,"13","American Samoa,Baker Island,Cook Islands,Fiji,French Polynesia,Howland Island,Jarvis Island,Kiribati,Marshall Islands,Micronesia,Nauru,New Caledonia,Niue,Samoa,Solomon Islands,Tonga,Tokelau,Tuvalu,Vanuatu,Wallis & Futuna"];



function initproject()
{
	m_pixelsPerLonDegree=16.0/360.0;
	m_negpixelsPerLonRadian = -(16.0/(2.0*Math.PI));
	m_bitmapOrigo=16.0/2.0;
	m_ww=m_bitmapOrigo*256*2;
}

var g_px,g_py;

function project(lon,lat)
{
	var e;

	g_px = (m_bitmapOrigo + lon * m_pixelsPerLonDegree)*256.0;
	e = Math.sin(lat*(Math.PI/180.0));
	e = Math.max(Math.min(e,0.9999),-0.9999);
	g_py=(m_bitmapOrigo + 0.5 * Math.log((1.0 + e) / (1.0 - e)) * m_negpixelsPerLonRadian)*256.0;
}

function setCookie(name,value,days)
{
	var expires;

	if (days)
	{
		var date = new Date();
		date.setTime(date.getTime()+(days*24*60*60*1000));
		expires = ";expires="+date.toGMTString();
	}
	else
		expires = "";
	document.cookie = name+"="+value+expires+"; path=/";
}

function getCookie(name)
{
	var nameEQ = name + "=";
	var ca = document.cookie.split(';');
	var e="";

	for(var i=0;i < ca.length;i++)
	{
		var c = ca[i];
		while (c.charAt(0)==' ')
			c = c.substring(1,c.length);
		if (c.indexOf(nameEQ) == 0)
			return c.substring(nameEQ.length,c.length);
	}
	return e;
}

function eraseCookie(name)
{
	setCookie(name,"",-1);
}

function country(xmlnode)
{
	var polys,i,j,points,e,pass,numpasses;
	var px,py,wminx,wmaxx,wminy,wmaxy,wcx,wcy;
	var tlat=0,tlon=0,slat=1,slon=1;

	//load country info

	this.shown=false;
	this.hide=false;
	this.name=xmlnode.getAttribute("name");
	this.color=xmlnode.getAttribute("color");
	if(xmlnode.getAttribute("expand")==null)
		this.expand=0;
	else
		this.expand=parseFloat(xmlnode.getAttribute("expand"));
	this.group=parseInt(xmlnode.getAttribute("group"));

	//special cases
	if(this.name=="Alaska")
	{
		tlon=-25;
		tlat=-40.5;
		slon=0.65;
		this.box=true;
	}
	else if(this.name=="Hawaii")
	{
		tlon=56;
		tlat=-2;
		this.box=true;
	}
	else
		this.box=false;

	//calc position to place country name (project lat/lon -> screen)
	project(tlon+slon*parseFloat(xmlnode.getAttribute("clon")),tlat+slat*parseFloat(xmlnode.getAttribute("clat")));
	this.namex=g_px;
	this.namey=g_py;

	polys = xmlnode.getElementsByTagName("poly");
	this.numpolys=polys.length;

	//for small islands we will expand the collision geometry if the pointer is close to make clicking easier
	if(this.expand)
		numpasses=2;
	else
		numpasses=1;

	for(pass=0;pass<numpasses;++pass)
	{
		if(!pass)
			this.polys=new Array(this.numpolys);
		else
			this.expolys=new Array(this.numpolys);

		for(i=0;i<polys.length;++i)
		{
			points=polys[i].innerHTML.split(",");	//comma seperate lon/lat

			coords=new Array(points.length);

			if(!pass)
			{
				this.polys[i]=coords;
			}
			else
			{
				/* since we are expanding this polygon we need to calculate its center */
				this.expolys[i]=coords;

				wminx=wmaxx=tlon+slon*parseFloat(points[0]);
				wminy=wmaxy=tlat+slat*parseFloat(points[1]);

				for(j=2;j<points.length;j+=2)
				{
					px=tlon+slon*parseFloat(points[j]);
					py=tlat+slat*parseFloat(points[j+1]);
					if(px<wminx)
						wminx=px;
					if(px>wmaxx)
						wmaxx=px;

					if(py<wminy)
						wminy=py;
					if(py>wmaxy)
						wmaxy=py;

				}
				/* center of this polygon (world coords) */
				wcx=(wminx+wmaxx)*0.5;
				wcy=(wminy+wmaxy)*0.5;
				project(wcx,wcy);
				this.cx=g_px;
				this.cy=g_py;
			}

			for(j=0;j<points.length;j+=2)
			{
				px=tlon+slon*parseFloat(points[j]);
				py=tlat+slat*parseFloat(points[j+1]);
				if(pass)
				{
					/* expand point out from center of polygon */
					px=((px-wcx)*this.expand)+wcx;
					py=((py-wcy)*this.expand)+wcy;
				}
				project(px,py);
				coords[j]=g_px;
				coords[j+1]=g_py;


				/* make a bounding box for mouse hilighting (so we can trivially skip the inside polygon check) */
				if(pass==0 && i==0 && j==0)
				{
					this.minx=this.maxx=coords[0];
					this.miny=this.maxy=coords[1];
				}
				else
				{
					if(coords[j]<this.minx)
						this.minx=coords[j];
					if(coords[j]>this.maxx)
						this.maxx=coords[j];

					if(coords[j+1]<this.miny)
						this.miny=coords[j+1];
					if(coords[j+1]>this.maxy)
						this.maxy=coords[j+1];
				}
			}
		}
	}
}

/* this is for the country name labels that are along the bottom of the screen */
function name(country,text,x,y,w,h)
{
	this.country=country;
	this.text=text;
	this.x=x;
	this.y=y;
	this.lx=x-w*0.5;
	this.rx=x+w*0.5;
	this.ty=y;
	this.by=y+h;
}

/* this is to re-draw the world and names along the bottom (on the base canvas), it is only called when new areas are exposed */
function draw()
{
	var i,c,p,j,coords;
	var tx,ty,sx,sy,dim;
	var w=canvas.width;
	var h=canvas.height;
	var pass,numpasses,tw,gap;
	var cw=new Array();

	context.shadowOffsetX = 0;
	context.shadowOffsetY = 0;
	context.shadowBlur = 0;
	context.shadowColor = "rgba(0, 0, 0, 0.5)";

	context.fillStyle = "rgb(218, 250, 251)";
	context.fillRect (0, 0, w,h);

	if(m_demo==false)
	{
		/* draw waves
		for(ty=0;ty<h;ty+=30)
		{
			for(tx=ty%40;tx<w;tx+=40)
			{
				context.strokeStyle = "rgba(255,255,255,0.35)";
				context.beginPath();
				context.arc(tx,ty,6,0,Math.PI*0.5,false);
				context.stroke();
				context.strokeStyle = "rgba(0,0,0,0.25)";
				context.beginPath();
				context.arc(tx+12,ty,6,Math.PI,Math.PI*0.5,true);
				context.stroke();
			}
		} */
	}

	if(m_x<0)
		numpasses=2;
	else
		numpasses=1;

	for(pass=0;pass<numpasses;++pass)
	{
		if(!pass)
			tw=0;
		else
			tw=(m_ww*m_ws);

		for(i=0;i<m_countries.length;++i)
		{
			c=m_countries[i];
			if(c.group==m_group)
			{
				for(p=0;p<c.numpolys;++p)
				{
					coords=c.polys[p];

					context.beginPath();
					context.moveTo(((coords[0]*m_s)-m_x)-tw,(coords[1]*m_s)-m_y);
					for(j=2;j<coords.length;j+=2)
					{
						context.lineTo(((coords[j]*m_s)-m_x)-tw,(coords[j+1]*m_s)-m_y);
					}
					context.closePath();
					if(c.hide)
					{
						context.fillStyle = "#E3E1C4";
						context.fill();
						context.strokeStyle = "rgba(0,0,0,0.2)";
					}
					else if(c.shown)
					{
						context.fillStyle = c.color;
						context.fill();
						context.strokeStyle = "rgba(50,0,0,0.5)";
					}
					else
					{
						context.fillStyle = "grey";
						context.fill();
						context.strokeStyle = "rgba(0,0,0,0.4)";
					}
					context.stroke();
				}
			}
		}
	}
	context.font = 'italic '+m_namesize+'px sans-serif';
	context.textBaseline = 'top';
	context.textAlign = 'center';

	/* draw map names */
	if(m_demo==false)
	{
		context.fillStyle = "black";
		for(pass=0;pass<numpasses;++pass)
		{
			if(!pass)
				tw=0;
			else
				tw=(m_ww*m_ws);
			for(i=0;i<m_countries.length;++i)
			{
				c=m_countries[i];


				if(c.group==m_group && c.shown && c.hide==false)
				{
					context.fillText(c.name, ((c.namex*m_s)-m_x)-tw,(c.namey*m_s)-m_y);
				}
			}
		}

	}

	/* draw any boxes for translated areas */

	context.strokeStyle = "white";
	m_numnames=0;
	for(i=0;i<m_countries.length;++i)
	{
		c=m_countries[i];

		if(c.group==m_group && c.box && c.hide==false)
		{
			context.beginPath();
			context.moveTo(((c.minx*m_s)-m_x)-1,((c.miny*m_s)-m_y)-1);
			context.lineTo(((c.maxx*m_s)-m_x)+1,((c.miny*m_s)-m_y)-1);
			context.lineTo(((c.maxx*m_s)-m_x)+1,((c.maxy*m_s)-m_y)+1);
			context.lineTo(((c.minx*m_s)-m_x)-1,((c.maxy*m_s)-m_y)+1);
			context.closePath();
			context.stroke();
		}
	}


	if(!m_demo)
	{
		context.fillStyle = "white";
		context.fillRect (0, h*0.8, w,h);
		context.fillStyle = "black";
		context.fillRect (0, h*0.8, w,1);
	}

	context.font = 'italic '+Math.floor(m_ws*12)+'px sans-serif';

	/* draw click names */
	context.fillStyle = "black";
	m_numnames=0;
	for(pass=0;pass<2;++pass)
	{
		tx=0;
		ty=0;
		if(pass)
		{
			/* calc column positions */
			gap=0.02;
			do
			{
				tw=0;
				for(i=0;i<cw.length;++i)
				{
					if(i)
						tw+=(w*gap);
					tw+=cw[i];
				}
				if(tw<=w)
					break;
				gap-=0.01;
			}while(true);
			sx=(w-tw)*0.5;
			for(i=0;i<cw.length;++i)
			{
				sx+=cw[i];
				if(i)
					sx+=(w*0.02);
				cw[i]=sx-(cw[i]*0.5);
			}
		}
		for(i=0;i<m_countries.length;++i)
		{
			c=m_countries[i];

			if(c.group==m_group && !c.shown && c.hide==false)
			{
				dim=context.measureText(c.name);
				if(!pass)
				{
					if(!ty)
						cw[tx]=dim.width;
					else
					{
						if(dim.width>cw[tx])
							cw[tx]=dim.width;
					}
				}
				else
				{
					sx=cw[tx];
					sy=(h*0.82)+(h*0.025*ty);
					context.fillText(c.name, sx,sy);
					m_names[m_numnames++]=new name(i,c.name,sx,sy,dim.width,12*m_ws);
				}
				if(++ty==7)
				{
					ty=0;
					++tx;
				}
			}
		}
	}

	if(!m_numnames)
	{
		if(m_demo)
		{
			if(m_showscores)
			{
				var x1=w*0.15;
				var x2=w*0.55;
				var x3=w*0.75;
				var x4=w*0.85;
				var lh=Math.floor(m_ws*23);
				var lh2=Math.floor(lh*1.10);
				var xx=w*0.03;

				context.textAlign = 'left';
				context.font = 'italic '+lh+'px sans-serif';
				y=h*0.1;
				context.fillStyle = "rgba(0,0,0,0.6)";
				context.fillRect (x1-xx, y-(xx*0.5),(x4+xx)-(x1-xx),(lh2*(m_scores.length+1))+xx);
				context.fillStyle = "white";
				for(i=-1;i<m_scores.length;++i)
				{
					if(i<0)
					{
						/* header */
						context.fillText("Region", x1,y);
						context.fillText("Time", x2,y);
						context.fillText("Errors", x3,y);
					}
					else
					{
						context.fillText(m_scores[i].name, x1,y);
						if(m_scores[i].time>0)
						{
							context.fillText(m_scores[i].time, x2,y);
							context.fillText(m_scores[i].errors, x3,y);
						}
					}
					y+=lh2;
				}
				context.textAlign = 'center';
				context.fillStyle = "black";
			}


			context.font = 'italic '+Math.floor(m_ws*23)+'px Helvetica';
			context.fillStyle = "rgba(0,0,0,0.6)";
			context.fillRect(w*0.1, h*0.86,w*0.8,h*0.10);
			context.fillStyle = "white";
			context.fillText("Select a Region using the pulldown menu.", w*0.5,h*0.87);
			context.fillText("Then drag each name to it's proper place on the map", w*0.5,h*0.91);
		}
		else
		{
			if(m_showall)
			{
				context.font = 'italic '+Math.floor(m_ws*15)+'px sans-serif';
				context.fillText("Press the Re-Start button to begin.", w*0.5,h*0.85);
			}
			else
			{
				/* sucess! */
				if(!m_finished)
				{
					var scores,better;

					m_time=Math.floor((new Date().getTime()-m_start)/1000);
					m_finished=true;
					//playSFX("tada",1.0);

					/* update the high score cookies */
					if(m_scores[m_level].time==0)
						better=true;
					else if(m_time<m_scores[m_level].time)
						better=true;
					else if((m_time==m_scores[m_level].time) && (m_errors<m_scores[m_level].errors))
						better=true;
					else
						better=false;

					if(better)
					{
						m_scores[m_level].time=m_time;
						m_scores[m_level].errors=m_errors;

						/* save a cookie */
						scores="";
						for(i=0;i<m_scores.length;++i)
						{
							if(scores.length)
								scores+=',';
							scores+=''+m_scores[i].time+','+m_scores[i].errors;
						}
						setCookie('scores',scores,365*10);
					}

				}
				context.font = 'italic '+Math.floor(m_ws*80)+'px sans-serif';
				context.fillText("Finished!", w*0.5,h*0.81);
				context.font = 'italic '+Math.floor(m_ws*25)+'px sans-serif';
				context.fillText("Time: "+m_time+" seconds, with "+m_errors+" errors", w*0.5,h*0.95);
			}
		}
	}

	context.shadowOffsetX=0;
	context.shadowOffsetY=0;
	context.shadowBlur = 0;
}

/* is point inside of poly? */
function checkInside(coords,px,py)
{
	var i,j=0;
	var odd=false;

	for(i=0;i<coords.length;i+=2)
	{
		j+=2;
		if (j==coords.length)
			j=0;
		if (coords[i+1]<py && coords[j+1]>=py || coords[j+1]<py && coords[i+1]>=py)
		{
			if (coords[i]+(py-coords[i+1])/(coords[j+1]-coords[i+1])*(coords[j]-coords[i])<px)
			{
				odd=!odd;
			}
		}
	}
	return (odd);
}


function mouseDown(ev)
{
	mpress=true;
	updateOverlay();
	mpress=false;
}

function mouseUp(ev)
{
	mrelease=true;
	updateOverlay();
	mrelease=false;
}


function updateCursor(ev)
{
	if (ev.layerX || ev.layerX === 0)
	{
		/* Firefox */
		ev._x=ev.layerX-canvas.offsetLeft;
		ev._y=ev.layerY-canvas.offsetTop;
	}
	else if (ev.offsetX || ev.offsetX === 0)
	{
		/* Opera */
		ev._x=ev.offsetX;
		ev._y=ev.offsetY;
	}
	mx=ev._x;
	my=ev._y;

	updateOverlay();
}

/* this updates based on mouse input and redraws the overlay canvas */
function updateOverlay()
{
	var i,c,wx,wy,j,coords,name,snd,over=-1;
	var w=ocanvas.width,h=ocanvas.height;
	var polyset,bh,pass,numpasses,wx;

	ocontext.clearRect(0, 0, w,h);

	ocontext.font = 'italic '+Math.floor(m_ws*12)+'px sans-serif';
	ocontext.shadowOffsetX = 1;
	ocontext.shadowOffsetY = 1;
	ocontext.shadowBlur = 2;
	ocontext.shadowColor = "rgb(128,128,128)";

	if(m_demo)
		by=h;
	else
		by=h*0.8;

	if(m_x<0)
		numpasses=2;
	else
		numpasses=1;

	if((m_place>=0 || m_showall) && mx>=0 && mx<w && !m_demo)
	{
		/* is mouse over the map area? */
		if(my>=0 && my<by)
		{
			/* convert mouse position to world position */
			wx=(mx+m_x)/m_s;
			wy=(my+m_y)/m_s;

			if(wx<0)
				wx+=m_ww;

			/* over = last country in list that mouse is over (this handles countries inside of countries) */
			for(i=0;i<m_countries.length;++i)
			{
				c=m_countries[i];
				if(c.group==m_group && (!c.hide || cheat) && c.numpolys && (!c.shown || m_showall))
				{

					if(wx>=c.minx && wx<=c.maxx && wy>=c.miny && wy<c.maxy)
					{
						if(c.expand)
							polyset=c.expolys;
						else
							polyset=c.polys;
						for(p=0;p<c.numpolys;++p)
						{
							if(checkInside(polyset[p],wx,wy))
							{
								if(over<0)
									over=i;
								else
								{
									/* smaller country has priority for overlapping countries */
									if(m_countries[i].expand>m_countries[over].expand)
										over=i;
								}
								break;
							}
						}
					}
				}
			}
			if(over>=0)
			{
				c=m_countries[over];

				if(mrelease && !m_showall)
				{
					/* is the mouse button pressed? */
					if(m_place>=0)
					{
						name=m_names[m_place];
						m_place=-1;
						if(name.country==over)
						{
							/* sucess! */
							c.shown=true;
							//playSFX("bleep",1.0);
							draw();
							inside=false;
						}
						else
						{
							++m_errors;
							//playSFX("buzzer",0.5);
						}
					}
				}
				else
				{
					/* debug setting */
					if(cheat)
					{
						ocontext.font = 'italic '+m_namesize+'px sans-serif';
						ocontext.fillStyle = "white";
						ocontext.textBaseline = 'top';
						ocontext.textAlign = 'left';
						ocontext.shadowOffsetX = 0;
						ocontext.shadowOffsetY = 0;
						ocontext.shadowBlur = 0;
						ocontext.shadowColor = "rgb(0,0,0)";
						ocontext.fillText(c.name, mx+10,my-20);
					}

					for(pass=0;pass<numpasses;++pass)
					{
						if(!pass)
							wx=0;
						else
							wx=(m_ww*m_ws);

						/* pointer is over the country */
						for(p=0;p<c.numpolys;++p)
						{
							coords=c.polys[p];
							ocontext.beginPath();
							ocontext.moveTo(((coords[0]*m_s)-m_x)-wx,(coords[1]*m_s)-m_y);
							for(j=2;j<coords.length;j+=2)
							{
								ocontext.lineTo(((coords[j]*m_s)-m_x)-wx,(coords[j+1]*m_s)-m_y);
							}
							ocontext.closePath();
							ocontext.strokeStyle = "rgba(255,0,0,0.75)";
							ocontext.stroke();
						}
						if(m_showall)
						{
							var nx=((c.namex*m_s)-m_x)-wx;
							var ny=(c.namey*m_s)-m_y;

							/* draw name in white */
							ocontext.font = 'italic '+m_namesize+'px sans-serif';
							ocontext.textBaseline = 'top';
							ocontext.textAlign = 'center';
							ocontext.shadowOffsetX = 0;
							ocontext.shadowOffsetY = 0;
							ocontext.shadowBlur = 0;
							ocontext.shadowColor = "rgb(0,0,0)";
							ocontext.fillStyle = "white";
							ocontext.fillText(c.name, nx-1,ny);
							ocontext.fillText(c.name, nx-1,ny-1);
							ocontext.fillText(c.name, nx,ny-1);
							ocontext.fillText(c.name, nx+1,ny-1);
							ocontext.fillText(c.name, nx+1,ny);
							ocontext.fillText(c.name, nx+1,ny-1);
							ocontext.fillText(c.name, nx,ny+1);
							ocontext.fillText(c.name, nx-1,ny+1);
							ocontext.fillStyle = "black";
							ocontext.fillText(c.name, nx,ny);
						}
					}
				}
			}
			if(m_place>=0)
			{
				/* draw name at cursor position */
				name=m_names[m_place];

				ocontext.font = 'italic '+Math.floor(m_ws*12)+'px sans-serif';
				ocontext.fillStyle = "white";
				ocontext.textBaseline = 'top';
				ocontext.textAlign = 'left';
				ocontext.shadowColor = "rgb(0,0,0)";
				ocontext.fillText(name.text, mx+10,my-10);
			}
		}

	}
	ocontext.shadowOffsetX = 1;
	ocontext.shadowOffsetY = 1;
	ocontext.shadowBlur = 2;
	ocontext.shadowColor = "rgb(128,128,128)";
	ocontext.fillStyle = "rgba(0,0,0,0)";


	/* draw circle around all unhidden and unshown countries with expand>3 */
	for(i=0;i<m_countries.length;++i)
	{
		c=m_countries[i];
		if(c.group==m_group && c.expand>3 && c.shown==false && c.hide==false && c.numpolys)
		{
			for(pass=0;pass<numpasses;++pass)
			{
				if(!pass)
					wx=0;
				else
					wx=(m_ww*m_ws);
				ocontext.beginPath();
				ocontext.arc(((c.cx*m_s)-m_x)-wx,((c.cy*m_s)-m_y),6,0,Math.PI*2,true);
				ocontext.closePath();
				if(i==over)
					ocontext.strokeStyle = "rgba(255,0,0,0.75)";
				else
					ocontext.strokeStyle = "rgba(160,25,25,0.75)";
				ocontext.stroke();
			}
		}

	}


	if(!m_demo)
	{
		ocontext.clearRect(0, h*0.8, w,h*0.2);

		/* selecting a country name? */
		if(mx>=0 && mx<w && my>=(h*0.8) && my<h)
		{
			if(mpress)
				m_place=-1;

			for(i=0;i<m_numnames;++i)
			{
				name=m_names[i];
				if(mx>=name.lx && mx<=name.rx && my>=name.ty && my<=name.by)
				{
					ocontext.shadowColor = "rgba(255,0,0, 0.5)";
					ocontext.fillStyle = "Red";
					ocontext.textBaseline = 'top';
					ocontext.textAlign = 'center';
					ocontext.fillText(name.text, name.x,name.y);
					if(mpress)
					{
						//playSFX("bleep",0.2);
						m_place=i;
					}
					break;
				}
			}
		}
	}

	ocontext.shadowOffsetX=0;
	ocontext.shadowOffsetY=0;
	ocontext.shadowBlur = 0;
}

/* update the canvas size */
function newSize(redraw)
{
	var sel =  1.25;

	//sel=document.getElementById('size');
	m_ws=parseFloat(sel);

	ocanvas.width=canvas.width=Math.floor(720*m_ws);
	ocanvas.height=canvas.height=Math.floor(540*m_ws);

	m_s=g_regions[m_index+1]*m_ws;
	m_x=g_regions[m_index+2]*m_ws;
	m_y=g_regions[m_index+3]*m_ws;
	m_namesize=Math.floor(g_regions[m_index+4]*m_ws);
	if(redraw)
	{
		draw();
		updateOverlay();
	}
}


function newGame()
{
	var i,j,sel;
	var hide,ss,showlist;

	m_errors=0;
	m_start=new Date().getTime();

	m_showall=false;
	m_finished=false;
	m_place=-1;
	//sel=document.getElementById('group');
	//m_level=parseInt(sel.options[sel.selectedIndex].value);
	m_level=8;
	m_index=m_level*6;

	//scale, tx,ty
	m_group=g_regions[m_index];
	newSize(false);
	ss=g_regions[m_index+5];	//list of countries to show
	showlist=ss.split(",");		//split into an array

	if(m_level<2)
	{
		//demo screen
		m_demo=true;
		m_showscores=(m_level==1);
		m_showall=true;
		for(i=0;i<m_countries.length;++i)
		{
			c=m_countries[i];
			c.hide=false;
			c.shown=true;
		}
	}
	else
	{
		m_demo=false;
		m_showscores=false;
		//hide all countries with no polys
		for(i=0;i<m_countries.length;++i)
		{
			c=m_countries[i];

			hide=true;
			if(c.numpolys==0)
				hide=true;
			if(ss=='*')
				hide=false;
			else
			{
				for(j=0;j<showlist.length;++j)
				{
					if(showlist[j]==c.name)
						hide=false;
				}
			}
			c.hide=hide;
			c.shown=false;
		}
	}
	draw();
	updateOverlay();
}

function showAll()
{
	var i;

	m_showall=true;
	m_place=-1;
	for(i=0;i<m_countries.length;++i)
		m_countries[i].shown=true;
	draw();
	updateOverlay();
}

function init()
{
	var i,xmldata,sel,ss,scores;

	// Find the canvas element.
	canvas = document.getElementById('carea');
	if (!canvas)
	{
		alert('Error: I cannot find the canvas element!');
		return;
	}

	// Get the 2D canvas context.
	context = canvas.getContext('2d');
	if (!context)
	{
		alert('Error: failed to getContext!');
		return;
	}

	//overlay canvas
	ocanvas = document.getElementById('oarea');
	ocontext = ocanvas.getContext('2d');

	initproject();

	/* init the scores */
	sel=1
	m_scores=new Array(sel);
	for(i=0;i<m_scores.length;++i)
	{
		m_scores[i]=new Array();
		m_scores[i].name="Middle East";
		m_scores[i].time=0;
		m_scores[i].errors=0;
	}
	/* load the scores from the score cookie */
	ss=getCookie('scores');
	if(ss.length)
	{
		var scores=ss.split(",");
		var ne=scores.length/2;

		for(i=0;i<ne;++i)
		{
			//m_scores[i].time=parseInt(scores[i<<1]);
			//m_scores[i].errors=parseInt(scores[(i<<1)+1]);
		}
	}

	//the XML data is 620k if embedded as text, but packed into a png it's 289k (plus 25% more for base64)
	//extract the xml data from inside the base64 encoded png image (it's stoLimeGreen in the rgb pixels)
	if(0)
	{
		var image=document.getElementById('data');
		var w=image.width;
		var h=image.height;
		var cd,dp;
		var datalen;
		var s="";
		var v;
		var xmlblock;

		//draw the image to the canvas
		context.drawImage(image,0,0);

		try
		{
			cd=context.getImageData(0,0,w,h);
		}
		catch(err)
		{
			//browser doesn't support getImageData
			alert("Error: Sorry, your browser doesn't support canvas.getImageData! error="+err);
			return;
		}

		dp=cd.data;

		datalen=dp[0]+(dp[1]<<8)+(dp[2]<<16);

		v=4;
		for(i=0;i<datalen;++i)
		{
			s+=String.fromCharCode(dp[v]);
			++v;
			/* skip the alpha channel */
			if((v&3)==3)
				++v;
		}

		xmlblock=document.createElement("xml");
		xmlblock.innerHTML=s;
		xmldata = xmlblock.getElementsByTagName("trk");
	}
	else
	{
		//parse map data
		xmldata = document.getElementById('xmldata').getElementsByTagName("trk");
	}

	m_countries=new Array(xmldata.length);
	var out="";
	for(i=0;i<m_countries.length;++i)
	{
		m_countries[i]=new country(xmldata[i]);
		if(cheat)
		{
			var j,k,ss,showlist,used;

			if(m_countries[i].numpolys==0)
				out+="No Polys:"+m_countries[i].name+"\n";
			else if(m_countries[i].group==0)
			{
				used=false;
				for(j=0;j<15;++j)
				{
					ss=g_regions[(j*6)+5];		//list of countries to show
					showlist=ss.split(",");		//split into an array
					for(k=0;k<showlist.length;++k)
					{
						if(showlist[k]==m_countries[i].name)
							used=true;
					}
				}
				if(!used)
					out+="Not Used:"+m_countries[i].name+"\n";
			}
		}



	}

	ocanvas.onmousemove=updateCursor;
	ocanvas.onmousedown=mouseDown;
	ocanvas.onmouseup=mouseUp;
	//newVolume();
	newGame();
	if(cheat)
		alert(out);
}
