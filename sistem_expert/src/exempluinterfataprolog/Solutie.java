/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package exempluinterfataprolog;

import java.util.Map;

/**
 *
 * @author Lenovo
 */
public class Solutie 
{
    public String nume;
    public String factorCertitudine;
    public String descriere;
    public Map<String, String> proprietati;
    public String URL;
    
    public Solutie(String nume, String factorCertitudine, String descriere, Map<String, String> proprietati, String URL)
    {
        this.nume = nume;
        this.factorCertitudine = factorCertitudine;
        this.descriere = descriere;
        this.proprietati = proprietati;
        this.URL = URL;
    }
}
