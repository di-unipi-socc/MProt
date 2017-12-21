<p align="left">
  <img src="img/barrel-logo.png" width="300"/>
</p>


## What is Barrel?
Barrel is a web-based application that permits ediiting and analysing fault-aware management protocols in composite applications specified in [TOSCA](http://docs.oasis-open.org/tosca/TOSCA/v1.0/TOSCA-v1.0.html).

A running instance of Barrel is available at [http://di-unipi-socc.github.io/barrel/](http://di-unipi-socc.github.io/barrel/). 

## How to use Barrel
### Setting the stage
The very first step is to import a [CSAR](http://docs.oasis-open.org/tosca/TOSCA/v1.0/os/TOSCA-v1.0-os.html#_Toc356403711) package containing the TOSCA application to be edited and/or analysed. Once a CSAR is loaded, the corresponding application can be visualised, edited, and analysed through the corresponding __Visualise__, __Edit__, and __Analyse__ panes.

Sample CSARs concerning the application in the below figure are available in this repository.

![Thinking application](https://raw.githubusercontent.com/di-unipi-socc/barrel/master/examples/thinking-app.png)

They can be found in the [examples](https://github.com/di-unipi-socc/barrel/tree/master/examples) folder:
* [thinking-app-without-protocols.csar](https://github.com/di-unipi-socc/barrel/raw/master/examples/thinking-app-without-protocols.csar) is the CSAR modelling the application, without specifying any management protocol.
* [thinking-app.csar](https://github.com/di-unipi-socc/barrel/raw/master/examples/thinking-app.csar) is the CSAR modelling the application, by also specifying examples of fault-aware management protocols for its components (without specifying any fault-handling transition).
* [thinking-app-with-fault-handlers.csar](https://github.com/di-unipi-socc/barrel/raw/master/examples/thinking-app-with-fault-handlers.csar) is the CSAR modelling the application, by also specifying examples of fault-aware management protocols for its components (including fault-handling transition).

### Visualising applications

The __Visualise__ pane:
* graphically displays the application topology (on the left hand side of the pane), and
* provides further information about each application component in a table (one the right hand side of the pane). 

### Editing applications

The __Edit__ pane permits editing the fault-aware management protocols of the nodes in the application topology. 
The __Management protocol editor__ permits selecting the node type to be edited. 
Once a node type is selected, its fault-aware management protocol is displayed, and it can be edited with the toolbars right below it.

### Analysing applications

The __Analyse__ pane permits interactively analysing the fault-aware management behaviour of the composite application in the imported CSAR.
* The __Option__ section permits configuring the analysis context (e.g., by enabling/disabling hard recovery) 
* The __Simulator__ section contains a table that permits interactively simulating the behaviour of the composite application. More precisely, the __Simulator__ allows to simulate sequences of operation/fault-handling transitions, hence permitting to determine their effects on the whole application. 
* The __Planner__ permits specifying two different configurations of the imported composite  application (*source global state* and *target global state*), and it displays the sequence of operation/fault-handling transitions that leads from the *source global state* to the *target global state*.

## About
This repository contains the source code of the implementation of modelling and analysis approaches presented in 
> _A. Brogi, A. Canciani, J. Soldani <br>
> **Fault-aware management protocols for composite applications** <br>
> Submitted for publication._ 

If you wish to reuse the sources in this repository, please properly cite the above mentioned paper. Below you can find the BibTex reference:
```
@article{fault-aware-management-protocols,
  author = {Antonio Brogi and Andrea Canciani and Jacopo Soldani},
  title = {Fault-aware management protocols for composite applications},
  note = {[Submitted for publication]}
}
```
