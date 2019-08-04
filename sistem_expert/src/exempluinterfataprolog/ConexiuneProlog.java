/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package exempluinterfataprolog;

import exempluinterfataprolog.*;
import java.io.IOException;
import java.io.InputStream;
import java.io.PipedOutputStream;
import java.io.PrintStream;
import java.net.ServerSocket;
import java.net.Socket;

/**
 *
 * @author Irina
 */
public class ConexiuneProlog {
    final String caleExecutabilSicstus="H:\\Facultate\\Sisteme Expert\\ia\\SICStus Prolog 4.0.2\\bin\\spwin.exe";
    final String nume_fisier="sistem_expert_carte.pl";
    //final String nume_fisier="ceva_simplu.pl";    
    final String scop="inceput.";    
    //final String scop="main.";

    Process procesSicstus;
    ExpeditorMesaje expeditor;
    CititorMesaje cititor;
    FereastraMea fereastra;
    ServerSocket servs;
    int port;
    
    
    public FereastraMea getFereastra(){
        return fereastra;
    }
    
    public ConexiuneProlog(int _port, FereastraMea _fereastra) throws IOException, InterruptedException{
        InputStream processIs, processStreamErr;
        port=_port;
        fereastra=_fereastra;
        servs = new ServerSocket(port);
        //Socket sock_s=servs.accept();
        cititor=new CititorMesaje(this,servs);
        cititor.start();
        expeditor=new ExpeditorMesaje(cititor);
        expeditor.start();
        
        
        Runtime rtime= Runtime.getRuntime();
        
        String comanda = caleExecutabilSicstus + " -f -l " + nume_fisier + " --goal " + scop + " -a " + port;
         
        procesSicstus=rtime.exec(comanda);
        
        //InputStream-ul din care citim ce scrie procesul
        processIs=procesSicstus.getInputStream();
        //stream-ul de eroare
        processStreamErr=procesSicstus.getErrorStream();
        
        
        

    }
    
    void opresteProlog() throws InterruptedException{
        PipedOutputStream pos= this.expeditor.getPipedOutputStream();
        PrintStream ps=new PrintStream(pos);
        ps.println("exit.");
        ps.flush();
    }
}
