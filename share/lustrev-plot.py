import base64
import datetime
import io
import argparse


import dash
import dash_core_components as dcc
import dash_html_components as html
import dash_table
from dash.dependencies import Input, Output, State

import plotly.express as px
import plotly.graph_objects as go
from plotly.subplots import make_subplots

import pandas as pd


parser = argparse.ArgumentParser(description='Launch dash app to display tubes.')
parser.add_argument('datacsv', metavar='data.csv', type=str, 
                    help='a csv file with bounds on signals')
args = parser.parse_args()

# initial load
init_df = pd.read_csv(args.datacsv,index_col=False)
init_df_json=init_df.to_json(date_format='iso', orient='split')
init_types=init_df['type'].unique()
init_typesel_options=[{'label': t, 'value': t} for t in init_types]
init_signals = init_df['varid'].unique()
init_signals_option = [{'label': i, 'value': i} for i in init_signals]

# TODO: retravailler le cas bool3 pour voir si on a des infos partitionnees
# TODO: generer une vrai figure par signal
# TODO: extraire les suffixes de contexte booleens pour construire, pour chaque signal, la liste des signaux de partitionnement


app = dash.Dash(__name__)

app.layout = html.Div([
    dcc.Upload(
        id='upload-data',
        children=html.Div([
            'Drag and Drop or ',
            html.A('Select Files')
        ]),
        style={
            'width': '100%',
            'height': '60px',
            'lineHeight': '60px',
            'borderWidth': '1px',
            'borderStyle': 'dashed',
            'borderRadius': '5px',
            'textAlign': 'center',
            'margin': '10px'
        },
        # Allow multiple files to be uploaded
        multiple=True
    ),
    dcc.Dropdown(
        id="signal_sel",
        options=[],
        multi=True,
        value = []
    ),
    dcc.Checklist(
        id="sameplotcheck",
        options=[
            {'label': 'Plot on same graph', 'value': 'samegraph'},
        ],
        value=[]
    ),
    dcc.Checklist(
        id="typesel",
        options=[], 
        value=[] 
    ),
    dcc.Graph(id="graph"),
    #html.Button("Switch Min/Max", id='btn', n_clicks=0),
    html.Div(id='selected-data'),    
    html.Div(id='output-data-upload'),    
    # Hidden div inside the app that stores the intermediate value
    #html.Div(children='Dash: A web application framework for Python.', style={
    #    'textAlign': 'center',
    #    'color': colors['text']
    #}),
    html.Div(id='global_df', style={'display': 'none'},
             children=init_df_json
             )
])

# # @app.callback(
# #     Output("graph", "figure"), 
# #     [Input("btn", "n_clicks")])
# # def display_graph(n_clicks):
# #     if n_clicks % 2 == 0:
# #         x, y = 'timestep', ' __lego_anti_windup_real_10_min'
# #     else:
# #         x, y = 'timestep', ' __lego_anti_windup_real_10_max'

# #     fig = px.line(df, x=x, y=y)    
# #     return fig


def onesigfig(fig,signal_df,name,row,col):
    color='rgba(0,250,0,0.4)'
    x, y_min, y_max = 'timestep', 'min', 'max'
    type=signal_df['type'].unique()
    fig.add_traces(
        go.Scatter(
            x = signal_df[x],
            y = signal_df[y_min],
            line = dict(color='rgba(0,0,0,0)',shape='hv'),
            name=None),
        rows=row,cols=col)
    fig.add_traces(
        go.Scatter(
            x = signal_df[x],
            y = signal_df[y_max],
            fill='tonexty',
            line = dict(shape='hv'),
            name=name,
            fillcolor =color),
        rows=row,cols=col)
    fig.add_traces(
        go.Scatter(
            x=signal_df[x],
            y = signal_df[y_max],
            line = dict(color = 'black', width=1,shape='hv'),
            name=name+'_max'),
        rows=row,cols=col)
    fig.add_traces(
        go.Scatter(
            x=signal_df[x],
            y = signal_df[y_min],
            mode='lines',
            line = dict(color = 'black', width=1,shape='hv'),
            name=name+'_min'),
        rows=row,
        cols=col)
    if type != 'bool':
        fig.update_yaxes(type='linear')
    return fig
    # fig.add_traces(go.Scatter(x = signal_df[x], y = signal_df[y_min],
    #                       line = dict(color='rgba(0,0,0,0)')))
    # fig.add_traces(go.Scatter(x = signal_df[x], y = signal_df[y_max],
    #                           fill='tonexty',
    #                           fillcolor =color))
    # fig.add_traces(go.Scatter(x=signal_df[x], y = signal_df[y_max],
    #                   line = dict(color = 'black', width=1)))
    # fig.add_traces(go.Scatter(x=signal_df[x], y = signal_df[y_min],
    #                   line = dict(color = 'black', width=1)))
    
    #fig = px.line(signal_df, x=x, y=[y_min,y_max],line_shape='hv')
    #, fill='tonexty')
    #    fig.add_scatter(df, x=x, y=y_max, mode='lines')

def extract_selection(df):
    children = html.Div([
        html.Hr(),  # horizontal line
        dash_table.DataTable(
            data=df.to_dict('records'),
            columns=[{'name': i, 'id': i} for i in df.columns]
        ),
        html.Hr(),  # horizontal line
    ])
    return children
        
        
# Changing dropdown menu or same/split view updates the figure
@app.callback(
    Output("graph", "figure"),
    Output('selected-data', 'children'),
    [Input("signal_sel", "value"),
     Input("sameplotcheck", "value"),
     Input("global_df", 'children')
     ])
def display_graph_signal(selection,checkval,jsonified):
    if 'samegraph' in checkval:
        plot_on_same_graph = True
    else:
        plot_on_same_graph = False
    color='rgba(0,250,0,0.4)'
    x, y_min, y_max = 'timestep', 'min', 'max'
    if selection is None or selection == [] or jsonified == None:
        return {}, None
        #selection=signals
    else:
        df=pd.read_json(jsonified, orient='split')
        if plot_on_same_graph:
            nb_rows=1
            fig = make_subplots(rows=nb_rows,
                                cols=1,
                                )
        else:
            nb_rows=len(selection)
            fig = make_subplots(rows=nb_rows,
                                cols=1,
                                subplot_titles=selection)
        for idx, sig in enumerate(selection):
            signal_df = df.query("varid=='" + sig + "'")
            if plot_on_same_graph:
                row_id=1
            else:
                row_id=idx+1
            onesigfig(fig,signal_df,sig,row_id,1)
        fig.update_layout(height=300 * nb_rows)
        signals_data=df.query("varid in " + str(selection))
        data=extract_selection(signals_data)
        return fig, data

# Changing global_df or choice of types updates dropdown menu
@app.callback(Output("signal_sel", "options"),
              Output("signal_sel", "value"),
              Input("global_df", 'children'),
              Input('typesel', 'value')
              )
def update_available_signals(jsonified, typesel):
    if jsonified == None:
        return [],[]
    else:
        df=pd.read_json(jsonified, orient='split')
        signals_data=df.query('type in ' +str(typesel))
        signals=signals_data['varid'].unique()
        signals_options=[{'label': i, 'value': i} for i in signals]
        return signals_options, signals


def parse_contents(contents, filename, date):
    content_type, content_string = contents.split(',')
    decoded = base64.b64decode(content_string)
    try:
        if 'csv' in filename:
            # Assume that the user uploaded a CSV file
            #print(decoded)
            df = pd.read_csv(
                io.StringIO(decoded.decode('utf-8')),
                index_col=False
            )
            #types=df['type'].unique()
            #signals = df['varid'].unique()
        
    except Exception as e:
        print(e)
        return None, [], [], html.Div([
            'There was an error processing this file.'
        ])

    return df, html.Div([
        html.H5(filename),
        html.H6(datetime.datetime.fromtimestamp(date)),

        dash_table.DataTable(
            data=df.to_dict('records'),
            columns=[{'name': i, 'id': i} for i in df.columns]
        ),

        html.Hr(),  # horizontal line

        # For debugging, display the raw contents provided by the web browser
        html.Div('Raw Content'),
        html.Pre(contents[0:200] + '...', style={
            'whiteSpace': 'pre-wrap',
            'wordBreak': 'break-all'
        })
    ])

# Loading new csv, updates types and global_df
@app.callback(Output("typesel", 'options'),
              Output("typesel", 'value'),
              Output("global_df", 'children'),
              Output('output-data-upload', 'children'),
              Input('upload-data', 'contents'),
              State('upload-data', 'filename'),
              State('upload-data', 'last_modified')
              )
def update_df_and_outputlog(list_of_contents, list_of_names, list_of_dates):
    if list_of_contents is not None:
        #args= zip(list_of_contents, list_of_names, list_of_dates)
        #c,n,d= args[0]
        df, children = parse_contents(list_of_contents[0], list_of_names[0], list_of_dates[0])
        # for c, n, d in
        
        df_json=df.to_json(date_format='iso', orient='split')
        types=df['type'].unique()
        typesel_options = [{'label': t, 'value': t} for t in types]
        return typesel_options, types, df_json, children
    else:
        return init_typesel_options, init_types, init_df_json, None
        
app.run_server(debug=True)
