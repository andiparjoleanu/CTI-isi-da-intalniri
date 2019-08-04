package exempluinterfataprolog;

/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */


import exempluinterfataprolog.*;
import java.io.IOException;
import java.io.InputStream;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.swing.SwingUtilities;

/**
 *
 * @author Irina
 */
public class CititorMesaje extends Thread {
    ServerSocket servs;
    volatile Socket s=null;//volatile ca sa fie protejat la accesul concurent al mai multor threaduri
    volatile PipedInputStream pis=null;
    ConexiuneProlog conexiune;

    //setteri sincronizati
    public synchronized void setSocket(Socket _s){
        s=_s;
        notify();
    }    
    
    public final synchronized void setPipedInputStream(PipedInputStream _pis){
        pis=_pis;
        notify();
    }
    //getteri sincronizati
    
    public synchronized Socket getSocket() throws InterruptedException
    {
        if (s==null){
            wait();//asteapta pana este setat un socket
        }
        return s;
    }
    
    public synchronized PipedInputStream getPipedInputStream() throws InterruptedException{
        if(pis==null){
            wait();
        }
        return pis;
    }
    
    
    //constructor
    public CititorMesaje(ConexiuneProlog _conexiune, ServerSocket _servs) throws IOException{
        servs=_servs;
        conexiune=_conexiune;
    }
    
    @Override
    public void run(){
        try {
            //apel blocant, asteapta conexiunea
            //conexiunea clinetului se face din prolog
            Socket s_aux=servs.accept();
            setSocket(s_aux);
            //pregatesc InputStream-ul pentru a citi de pe Socket
            InputStream is=s_aux.getInputStream();
            
            PipedOutputStream pos=new PipedOutputStream();
            setPipedInputStream(new PipedInputStream(pos,100000));//leg un pipedInputStream de capatul in care se scrie
            
            int chr;
            String str="";
            while((chr=is.read())!=-1) {//pana nu citeste EOF
                pos.write(chr);//pun date in Pipe, primite de la Prolog
                str+=(char)chr;
                if(chr=='\n'){
                    final String sirDeScris=str;
                    str="";
                    SwingUtilities.invokeLater(new Runnable() {
                        public void run(){ 
                            //conexiune.getFereastra().getDebugTextArea().append(sirDeScris); 
                            String text=sirDeScris.trim();
                            //verific daca e intrebare
                            if(text.length()>2 && text.charAt(0)=='i'&& text.charAt(1)=='(' && text.charAt(text.length()-1)==')')
                            {
                                String intrebare = text.substring(2, text.length()-1);
                                conexiune.getFereastra().setIntrebare(intrebare);
                            }
                            //verific daca sunt optiuni
                            else if(text.length()>2 && text.charAt(0)=='(' && text.charAt(text.length()-1)==')')
                            {
                                conexiune.getFereastra().setOptiuni(text);             
                            }
                            //verific daca e solutie
                            else if(text.length()>2 && text.charAt(0)=='s' && text.charAt(1)=='(' && text.charAt(text.length()-1)==')')
                            {
                                String solutie = text.substring(2, text.length()-1).replaceAll("'", "");
                                conexiune.getFereastra().adaugaSolutie(solutie);
                            }
                            else if(text.length()>2 && text.charAt(0)=='w' && text.charAt(1)=='(' && text.charAt(text.length()-1)==')')
                            {
                                String descriere = text.substring(2, text.length()-1).replaceAll("\\$", "\n");
                                conexiune.getFereastra().setCum(descriere);
                            }
                            else if(text.length()>2 && text.charAt(0)=='d' && text.charAt(1)=='(' && text.charAt(text.length()-1)==')')
                            {
                                String descriere = text.substring(2, text.length()-1).replaceAll("\\$", "\n");
                                conexiune.getFereastra().setDeCe(descriere);
                            }
                            else if(text.length()>2 && text.charAt(0)=='f' && text.charAt(1)=='(' && text.charAt(text.length()-1)==')')
                            {
                                String fapte = text.substring(2, text.length()-1).replaceAll("\\$", "\n");
                                conexiune.getFereastra().setFapte(fapte);
                            }
                        }

                    });
                }
            }
            
            
        } catch (IOException ex) {
            Logger.getLogger(CititorMesaje.class.getName()).log(Level.SEVERE, null, ex);
        }
    }
            
}
